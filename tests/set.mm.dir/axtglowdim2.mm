include "c2.mm"
include "cstrkgld.mm"
include "wbr.mm"
include "cv.mm"
include "co.mm"
include "wcel.mm"
include "w3o.mm"
include "wn.mm"
include "wrex.mm"
include "wb.mm"
include "istrkg2ld.mm"
include "syl.mm"
include "mpbid.mm"

theorem axtglowdim2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cV: class V
  let vu: setvar u
  let vv: setvar v
  assume axtrkge.p: |- P = ( Base ` G )
  assume axtrkge.d: |- .- = ( dist ` G )
  assume axtrkge.i: |- I = ( Itv ` G )
  assume axtglowdim2.v: |- ( ph -> G e. V )
  assume axtglowdim2.g: |- ( ph -> G TarskiGDim>= 2 )

  disjoint x y
  disjoint x z
  disjoint .- x
  disjoint y z
  disjoint .- y
  disjoint .- z
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .- u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint .- v
  disjoint I u
  disjoint I v
  disjoint P u
  disjoint P v
  assert |- ( ph -> E. x e. P E. y e. P E. z e. P -. ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) ) )

  proof
    wph
    cG
    c2
    cstrkgld
    wbr
    #
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cI
    co
    wcel
    @2
    @1
    @3
    cI
    co
    wcel
    @3
    @2
    @1
    cI
    co
    wcel
    w3o
    wn
    vz
    cP
    wrex
    vy
    cP
    wrex
    vx
    cP
    wrex
    #
    axtglowdim2.g
    wph
    cG
    cV
    wcel
    @0
    @4
    wb
    axtglowdim2.v
    vx
    vy
    vz
    cP
    cG
    cI
    c.mi
    cV
    axtrkge.p
    axtrkge.d
    axtrkge.i
    istrkg2ld
    syl
    mpbid
end
