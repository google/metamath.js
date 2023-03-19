
axiom ax-jca
  let tr: term R
  let ts: term S
  let tt: term T
  assume ax-jca.1: |- R |= S
  assume ax-jca.2: |- R |= T
  assert |- R |= ( S , T )
end
