
axiom ax-ded
  param tr: term R
  param ts: term S
  param tt: term T
  assume ax-ded.1: |- ( R , S ) |= T
  assume ax-ded.2: |- ( R , T ) |= S
  assert |- R |= ( ( = S ) T )
end
