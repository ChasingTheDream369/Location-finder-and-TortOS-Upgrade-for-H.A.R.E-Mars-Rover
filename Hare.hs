module Hare where

import Data.Word
import Data.List
import Control.Monad.State
import Test.QuickCheck
import Unsafe.Coerce 
import RoverInterface
import RoverModel

-- PART 1: FINDING WAYPOINTS

data Path wp
  = From wp
  | GoTo (Path wp) wp
  deriving (Eq)

instance Show wp => Show (Path wp) where
  show (From x) = "From " ++ show x
  show (GoTo xs x) = show xs ++ " >:> " ++ show x

-- Problem 1. Define a function `wf` that returns `True`
-- precisely if a given `Path` is well-formed according
-- to the rules set out in the specification.
findList :: Path wp -> [wp]
findList (From x) = [x]
findList (GoTo xs x) = (findList xs) ++ [x]

wf :: (Wp wp) => Path wp -> Bool
wf (From x) = True
wf (GoTo xs x) = (last (findList (xs)) `elem` navigableFrom x) && 
          ((length (nub (findList (GoTo xs x)))) == length (findList (GoTo xs x))) && wf(xs)
        
                               
-- Problm 2. Define a smart constructor `>:>` for `GoTo`
-- that returns `Nothing` if adding the given waypoint
-- to the given path would result in a non-well-formed path.
(>:>) :: (Wp wp) => Path wp -> wp -> Maybe (Path wp)
xs >:> x = if (wf (GoTo xs x))
          then (Just (GoTo xs x))
          else Nothing


-- Problem 3. Write a function `extendPath` which returns
-- all possible ways of extending the given `Path` by appending
-- a single additional waypoint.

extendPath :: (Wp wp) => Path wp -> [Path wp]
extendPath (xs) = [GoTo xs y | y <- navigableFrom (last (findList (xs))), wf (GoTo xs y)]

-- Problem 4. Implement a function `findPaths` which returns
-- all possible ways of extending the given `Path` (by appending
-- any number of additional waypoints) into a path that ends
-- at the given target waypoint.

findPaths :: (Wp wp) => Path wp -> wp -> [Path wp]
findPaths (xs) x 
              | (last (findList (xs)) == x)  = [xs]
              | otherwise = do
                          y <- extendPath (xs)
                          findPaths y x

-- Efficiency mark 5: your solution should not spend time
-- expanding "useless" partial solutions.




--- PART 2: DISK MATTERS - ENCODE/DECODE

-- The floppy disk drive has no means of tracking the
-- angular position of the spinning magnetic disk.
-- This means that in principle, reading/writing can
-- begin at any position within the track, and the
-- user has no control over where the reading/writing
-- starts from.

-- For example, if you write [1,2,3,4,5,6] on a track of
-- capacity 6, it can happend that reading the track next
-- time will result in [5,6,1,2,3,4] or [2,3,4,5,6,1]. Note
-- however that the disk can spin only in one direction, so
-- you will never get a result like [6,5,4,3,2,1].

-- In this subproblem, you will come up with an encoding
-- scheme gets around the problem of the spinning disk.

-- represents a list of bytes encoded using the scheme

data Encoded = Encoded [Word8] deriving (Show, Eq)

unEncoded :: Encoded -> [Word8]
unEncoded (Encoded ws) = ws

-- Problem 5. Implement a function `rotate` which simulates
-- the effect of the spinning disk by rotating the given
-- list to the left by the given number of entries. E.g.
-- rotate 3 (Encoded [1,2,3,4]) = Encoded [4,1,2,3]
-- Hint: for negative n, you get to choose the behavior.

rotate :: Int -> Encoded -> Encoded
rotate 0 (Encoded xs) = (Encoded xs)
rotate n (Encoded []) = Encoded ([])
rotate n (Encoded xs) | n < 0 = Encoded (take (length xs) (drop (n*(-1)) (cycle xs)))
        | otherwise = Encoded (drop (n `mod` length(xs)) xs ++ take (n `mod` length(xs)) xs)

rotate' :: Int -> [Word8] -> [Word8]
rotate' n [] = []
rotate' n xs = drop (n `mod` length(xs)) xs ++ take (n `mod` length(xs)) xs
-- Problem 6. Come up with an encoding scheme which gets
-- around the problem of the spinning disk. More formally,
-- implement a pair of functions, `encode` and `decode`, so
-- that:
--
-- 1. Decoding an encoded list of bytes results in the
-- original list, i.e. decode (encode bs) = Just bs.
-- 2. Decoding is rotationally invariant, i.e.
-- decode . rotate n . encode = Just for any positive n.

toWord8 :: Char -> Word8
toWord8 x = unsafeCoerce x

encode :: [Word8] -> Encoded
encode xs = Encoded ([1] ++ [1] ++ (concat ((map (\x -> [toWord8('a'), x]) (xs)))) ++ [toWord8('a')])

findDecode :: [Word8] -> [Word8]
findDecode xs = let (leftxs, rightxs) = splitAt (2) xs in
                      if (leftxs == [1,1]) then
                          let revRight = reverse (rightxs) in
                            let (Just lasta) = elemIndex 97 (revRight) in
                              [rightxs !! i | i <- [0..(length(rightxs)-1-lasta)], odd i]
                      else
                        findDecode (rotate' 1 xs)
    
decode :: Encoded -> Maybe [Word8]
decode (Encoded xs) = if (length (xs) < 3) then 
                        Nothing
                      else 
                        Just (findDecode (xs))

-- Efficiency mark: encoding a list of bytes with length
-- no more than 16 should result in an encoded list of
-- length no more than 37.


-- PART 3: FILE SYSTEM HIERARCHY

-- The rover's in-memory file system is organized into files and
-- directories. Each directory may contain other files and
-- directories inside it. Each file and directory is identified
-- by a unique `Word8`, its UID.


-- You can make the following assumptions about the file
-- system of the rover:
-- 1. The total size of all the files is no more than
--    16kiB (16384 bytes).
-- 2. Every file is at most 3072 bytes long.
-- 3. There are at most 48 files and directories (but their
--    UIDs need not be in the range 0-47) altogether.


-- We have decided that one track on the disk will store the
-- contents of at most one file, i.e. that there will not be
-- any tracks which store multiple files.

-- However, since floppy tracks store only 2048 bytes, and a
-- single file may be longer than 2048 bytes, we will have to
-- come up with a way of storing a single file across multiple
-- tracks.

-- We will divide each file into a list of chunks, so that each
-- chunk is short enough to be stored in a single track. We will
-- assign each chunk its own unique track.

-- To reassemble a file, we have to read and decode each of its
-- chunks from the disk in order, then concatenate the results.

data Chunk =
  Chunk TrackNo Encoded deriving (Show, Eq)

-- Problem 7. Write a stateful function `chunks` which,
-- when given the contents of a file, divides it into
-- a list of `Chunk`s.

-- The state `n` is a `TrackNo` between 0 and 255,
-- denoting the first track that is still available
-- to store data. E.g. if the state is 12, then
-- tracks 0-11 have already been used to store chunks,
-- but tracks 12-39 are still available. If all tracks
-- have been exhausted, signal the error by assiginng
-- the remaining chunks to track 40.

chunks :: [Word8] -> State TrackNo [Chunk]
chunks xs = do
          tracknum <- get
          let unencodedval = unEncoded (encode (xs))
          let (leftxs, rightxs) = splitAt 2048 (unencodedval)
          case rightxs of
            [] -> if (tracknum >= 40) then 
                    return ([Chunk (40) (Encoded (leftxs))])
                  else
                    put (tracknum+1) >>= \() -> return ([Chunk (tracknum) (Encoded (leftxs))])
                    
            xs -> let (leftxs1, rightxs1) = splitAt 2048 rightxs in
                    case rightxs1 of
                      [] -> if (tracknum >= 40) then 
                              return ([Chunk (40) (Encoded (leftxs)), Chunk (40) (Encoded (leftxs1))])
                            else if (tracknum == 39) then
                              put (tracknum+1) >>= \() ->
                              return ([Chunk (tracknum) (Encoded (leftxs)), Chunk (tracknum+1) (Encoded (leftxs1))])
                            else
                              put (tracknum+1) >>= \() -> put(tracknum + 2) >>= \() -> 
                              return ([Chunk (tracknum) (Encoded (leftxs)), Chunk (tracknum+1) (Encoded (leftxs1))])
                      xs -> let (leftxs2, rightxs2) = splitAt 2048 rightxs1 in
                              case rightxs2 of
                                [] -> if (tracknum >= 40) then
                                        return ([Chunk (40) (Encoded (leftxs)),
                                        Chunk (40) (Encoded (leftxs1)),
                                        Chunk (40) (Encoded (leftxs2))]) 
                                      else if (tracknum == 39) then
                                        put (tracknum+1) >>= \() ->
                                        return ([Chunk (tracknum) (Encoded (leftxs)),
                                        Chunk (tracknum+1) (Encoded (leftxs1)),
                                        Chunk (40) (Encoded (leftxs2))])
                                      else if (tracknum == 38) then
                                        put (tracknum+1) >>= \() -> put (tracknum + 2) >>= \() ->
                                        return ([Chunk (tracknum) (Encoded (leftxs)),
                                        Chunk (tracknum+1) (Encoded (leftxs1)),
                                        Chunk (40) (Encoded (leftxs2))])
                                      else 
                                        put (tracknum+1) >>= \() -> put(tracknum + 2) >>= \() -> 
                                        put(tracknum + 3) >>= \() -> 
                                        return ([Chunk (tracknum) (Encoded (leftxs)),
                                        Chunk (tracknum+1) (Encoded (leftxs1)),
                                        Chunk (tracknum+2) (Encoded (leftxs2))])
                                xs -> let (leftxs3, rightxs3) = splitAt 2048 rightxs2 in
                                        case rightxs3 of
                                          [] -> if (tracknum >= 40) then
                                                  return ([Chunk (40) (Encoded (leftxs)), 
                                                  Chunk (40) (Encoded (leftxs1)), 
                                                  Chunk (40) (Encoded (leftxs2)),
                                                  Chunk (40) (Encoded (leftxs3))]) 
                                                else if (tracknum == 39) then
                                                  put (tracknum + 1) >>= \() ->
                                                  return ([Chunk (tracknum) (Encoded (leftxs)), 
                                                  Chunk (tracknum+1) (Encoded (leftxs1)), 
                                                  Chunk (40) (Encoded (leftxs2)),
                                                  Chunk (40) (Encoded (leftxs3))])
                                                else if (tracknum == 38) then
                                                  put (tracknum + 1) >>= \() -> put (tracknum + 2) >>= \() ->
                                                  return ([Chunk (tracknum) (Encoded (leftxs)), 
                                                  Chunk (tracknum+1) (Encoded (leftxs1)), 
                                                  Chunk (tracknum+2) (Encoded (leftxs2)),
                                                  Chunk (40) (Encoded (leftxs3))])
                                                else if (tracknum == 37) then
                                                  put (tracknum + 1) >>= \() -> put (tracknum + 2) >>= \() ->
                                                  put (tracknum + 3) >>= \() ->
                                                  return ([Chunk (tracknum) (Encoded (leftxs)), 
                                                  Chunk (tracknum+1) (Encoded (leftxs1)), 
                                                  Chunk (tracknum+2) (Encoded (leftxs2)),
                                                  Chunk (tracknum+3) (Encoded (leftxs3))])    
                                                else 
                                                  put (tracknum+1) >>= \() -> put(tracknum + 2) >>= \() -> 
                                                  put(tracknum + 3) >>= \() -> put (tracknum + 4) >>= \() -> 
                                                  return ([Chunk (tracknum) (Encoded (leftxs)), 
                                                  Chunk (tracknum+1) (Encoded (leftxs1)), 
                                                  Chunk (tracknum+2) (Encoded (leftxs2)),
                                                  Chunk (tracknum+3) (Encoded (leftxs3))])
              

-- The `FSH t` data type represents a file system hierarchy
-- in which each file is annotated with data of type `t`.
-- For example, `FSH [Word8]` can be used to represent the
-- entire file system, where each file is annotated with its
-- contents (a list of bytes), while the type `FSH ()` can
-- be used to represent just the hierarchical relationships
-- between the files and directories (i.e. which contains
-- which), but without any of the file data.

-- Problem 8. Write a lawful Functor instance for the FSH
-- type.

instance Functor FSH where
  fmap g (File uid x) = File uid (g x)
  fmap g (Dir uid xs) = Dir uid [fmap g x | x <- xs]

-- We will have to save the whole directory hierarchy to
-- disk before the rover is rebooted. So that we can reassemble
-- the hierarchy, we will use Track 0 to store a "header". This
-- header will represent a `FSH [TrackNo]` object, where each
-- file is annotated with the list of tracks that contain its
-- chunks.

-- The `mkHeader` function below will create this header
-- from a file system hierarchy where each file has been
-- annotated with a list of its chunks (assuming your
-- `Functor` instance is correct).

mkHeader :: FSH [Chunk] -> FSH [TrackNo]
mkHeader = fmap (map (\(Chunk n _) -> n))


-- Problem 9. Implement a function `assignTracks` which divides
-- all files in a hierarchy into chunks. Each chunk should have
-- be assigned its unique track number. Do not allocate track 0,
-- as that will be used to store the header.
-- Return `Nothing` if the given file system would not fit on
-- tracks 1-39 of a 40-track disk under your encoding.
-- HINT: You'll probably want to have a separate function
-- with return type `State TrackNo (FSH [Chunk])`.
findNumBytes :: [FSH [Word8]] -> Int -> Int
findNumBytes [] n = n 
findNumBytes (x:xs) n = case x of
                        (File uid t) -> do
                                        let val = 2*(length(t)) + 3
                                        let numTracks = (val `div` 2048)
                                        findNumBytes (xs) (n + (numTracks +1))
                        
                        (Dir uid t) -> do
                                       let val = findNumBytes t n
                                       findNumBytes (xs) (val)

assignChunks :: FSH [Word8] -> (State TrackNo (FSH [Chunk]))
assignChunks (File uid x) = do 
                            track <- chunks (x)
                            return (File uid track)
                            
assignChunks (Dir uid (xs)) = sequence (map (assignChunks) xs) >>= \(seq) ->
                              return (Dir uid seq)


assignTracks :: FSH [Word8] -> Maybe (FSH [Chunk])
assignTracks xs =  case xs of 
                    (File uid t) -> Just(evalState (assignChunks xs) 1)
                    (Dir uid t) -> let val = findNumBytes t 0 in
                                    if (val > (39)) then
                                      Nothing
                                    else
                                      Just(evalState (assignChunks xs) 1)
          
-- PART 4 - DISK CONTROLLER

-- The disk controller supports four operations:
--   headForward - moves the read/write head forward by 1 track.
--   headBackward - moves the r/w head back toward zero by 1 track.
--   readTrack - reads 2048 consecutive bytes from the current track.
--   writeTrack - writes the given list of bytes to the current track.

-- In this problem, you will develop a program `saveFSH` that
-- uses this monad to save the entire file system onto the disk.

-- Problem 10. Write a program `headToTrack` that positions
-- the r/w head of the disk drive on the track with the given
-- number. If the number is larger than 39, position the head
-- on track 39.
moveHead :: (MonadFloppy m) => Word8 -> m ()
moveHead 0 = return ()
moveHead x = headForward >>= \() ->
                moveHead (x-1)
                
moveBackwards :: (MonadFloppy m) => Word8 -> m ()
moveBackwards 0 = return ()
moveBackwards x = headBackward >>= \() ->
                    moveBackwards (x - 1)
                    
headToTrack :: (MonadFloppy m) => Word8 -> m ()
headToTrack x | 
              (x <= 39) = (moveHead 39) >>= \() ->
                              moveBackwards(39 - x)
              | (x > 39) = (moveHead 39)
                

-- Problem 11. Write a program `saveChunk` which writes the
-- given chunk onto the appropriate track of the disk.
remJust :: (Maybe a) -> a
remJust (Just x) = x

saveChunk :: (MonadFloppy m) => Chunk -> m ()
saveChunk (Chunk t (Encoded e)) = do
                        headToTrack t
                        writeTrack (replicate 2048 0)
                        writeTrack ((e))


-- The function below calculates the header of the
-- given given `FSH [Chunk]`, and saves it to track 0
-- of the disk. Notice the use of the `toBytes` function.

saveHeader :: (MonadFloppy m) => FSH [Chunk] -> m ()
saveHeader fsh = do
  headToTrack 0
  writeTrack (replicate 2048 0)
  writeTrack (unEncoded $ encode $ toBytes $ mkHeader fsh)


-- Problem 12. Implement a program `saveFSH` that attemps to assign
-- track to the given `fsh` using `assignTracks`. If the assignment
-- was unsuccessful, the program should return False.
-- If the assignment was successful, the program should write the
-- header to track 0 of the disk, then write all the assigned chunks
-- onto the appropriate tracks.

writeChunks :: (MonadFloppy m) => FSH [Chunk] -> m ()
writeChunks (File uid []) = return ()
writeChunks (File uid (x:xs)) = do 
                                saveChunk x
                                writeChunks (File uid xs)
writeChunks (Dir uid []) = return ()
writeChunks (Dir uid (x:xs)) = do
                               writeChunks x
                               writeChunks (Dir uid xs)

saveFSH :: (MonadFloppy m) => FSH [Word8] -> m Bool
saveFSH xs = case assignTracks (xs) of
                Nothing -> return (False)
                Just (x) -> do
                            saveHeader x
                            writeChunks x
                            return (True)

-- Implement a program `loadFSH` that is able to reload a file
-- system from disk. I.e. if `saveFSH fsh` returns `True`, then
-- (saveFSH fsh >> loadFSH) should return `Just fsh`.
-- HINT: To load the header, you might want to use the `fromBytes`
--       function.
testval = [i | i <- [1..255]] ++ [i | i <- [1..255]] ++ [i | i <- [1..255]] ++ [i | i <- [1..255]] ++ [i | i <- [1..255]] ++ [i | i <- [1..255]] ++ [i | i <- [1..255]] ++ [i | i <- [1..255]] ++ [i | i <- [1..255]] ++ [i | i <- [1..255]] ++ [i | i <- [1..255]] ++ [i | i <- [1..255]]

test :: FSH [Word8]
test = Dir 0 [File 1 testval, File 2 testval, File 3 testval, File 4 testval, File 5 testval, File 6 testval, File 7 testval, File 8 testval, File 9 testval, File 10 testval, File 11 testval, File 12 testval, File 13 testval]

convertFSHTrack :: [Word8] -> Maybe (FSH [TrackNo]) 
convertFSHTrack xs = case (fromBytes (xs)) of
                      Nothing -> Nothing
                      Just x -> Just (fst (x))

getWord8List :: (MonadFloppy m) => Word8 -> [[Word8]] -> m ([[Word8]])
getWord8List (40) l = return (l)
getWord8List x l |
              (x <= 39) = do 
                          headToTrack x
                          t <- readTrack
                          getWord8List (x+1) (l ++ [(t)])

remZero :: [Word8] -> [Word8]
remZero xs = [x | x <- xs, x /= 0 ]

word8ToInt :: Word8 -> Int
word8ToInt = fromIntegral
                       
convertFileSystem :: [[Word8]] -> (FSH [TrackNo]) -> FSH [Word8]
convertFileSystem xs (File uid t) = do
                                    let val = [((xs) !! word8ToInt(track-1)) | track <- t]
                                    let decodedval = decode (Encoded (concat (val)))
                                    case decodedval of
                                      Just reqVal -> (File uid (reqVal))

convertFileSystem xs (Dir uid t) = (Dir uid (map (convertFileSystem xs) t))

loadFSH :: (MonadFloppy m) => m (Maybe (FSH [Word8]))
loadFSH = do
          headToTrack 0
          t <- readTrack
          let decodedTrack = (decode (Encoded t))
          case decodedTrack of
            Nothing -> return (Nothing)
            Just dTrack -> do
                            let convertedTrack = (convertFSHTrack (dTrack))
                            word8List <- (getWord8List 1 [])
                            case convertedTrack of
                              Nothing -> return (Nothing)
                              Just x -> do 
                                        let filesystem = convertFileSystem (word8List) (x)
                                        return (Just (filesystem))
  
  
testLoadFSH :: Maybe (FSH [Word8])
testLoadFSH = do
              let fsh = test
              let disk = emptyDisk
              let (_, disk') = runDiskModel (saveFSH fsh) disk
              let (fsh', _) = runDiskModel loadFSH disk'
              fsh'                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              