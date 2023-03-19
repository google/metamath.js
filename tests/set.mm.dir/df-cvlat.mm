
axiom df-cvlat
  let vk: setvar k
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assert |- CvLat = { k e. AtLat | A. a e. ( Atoms ` k ) A. b e. ( Atoms ` k ) A. c e. ( Base ` k ) ( ( -. a ( le ` k ) c /\ a ( le ` k ) ( c ( join ` k ) b ) ) -> b ( le ` k ) ( c ( join ` k ) a ) ) }
end
