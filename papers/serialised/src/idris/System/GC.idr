module System.GC

%default total

%foreign "scheme:collect"
prim__gc : Int -> PrimIO ()

export
gc : IO ()
gc = primIO $ prim__gc 4
