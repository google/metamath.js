include "neicvgnvor.mm"
include "neicvgmex.mm"

theorem neicvgnex
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vo: setvar o
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let cO: class O
  let vp: setvar p
  let vl: setvar l
  assume neicvg.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume neicvg.p: |- P = ( n e. _V |-> ( p e. ( ~P n ^m ~P n ) |-> ( o e. ~P n |-> ( n \ ( p ` ( n \ o ) ) ) ) ) )
  assume neicvg.d: |- D = ( P ` B )
  assume neicvg.f: |- F = ( ~P B O B )
  assume neicvg.g: |- G = ( B O ~P B )
  assume neicvg.h: |- H = ( F o. ( D o. G ) )
  assume neicvg.r: |- ( ph -> N H M )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint B n
  disjoint B o
  disjoint B p
  disjoint n o
  disjoint n p
  disjoint o p
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint n ph
  disjoint o ph
  disjoint p ph
  assert |- ( ph -> N e. ( ~P ~P B ^m B ) )

  proof
    wph
    cB
    cD
    cP
    vi
    vj
    vk
    vm
    vn
    vo
    cF
    cG
    cH
    cN
    cM
    cO
    vp
    vl
    neicvg.o
    neicvg.p
    neicvg.d
    neicvg.f
    neicvg.g
    neicvg.h
    wph
    cB
    cD
    cP
    vi
    vj
    vk
    vm
    vn
    vo
    cF
    cG
    cH
    cM
    cN
    cO
    vp
    vl
    neicvg.o
    neicvg.p
    neicvg.d
    neicvg.f
    neicvg.g
    neicvg.h
    neicvg.r
    neicvgnvor
    neicvgmex
end
