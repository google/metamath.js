include "cstrkg.mm"
include "wcel.mm"
include "cv.mm"
include "clng.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "co.mm"
include "w3o.mm"
include "crab.mm"
include "cmpt2.mm"
include "wceq.mm"
include "citv.mm"
include "wsbc.mm"
include "cbs.mm"
include "cab.mm"
include "cstrkgc.mm"
include "cstrkgb.mm"
include "cin.mm"
include "cstrkgcb.mm"
include "df-trkg.mm"
include "inss2.mm"
include "sstri.mm"
include "eqsstri.mm"
include "sseli.mm"
include "cvv.mm"
include "cds.mm"
include "eqid.mm"
include "istrkgl.mm"
include "simprbi.mm"
include "syl5eq.mm"
include "syl.mm"

theorem tglng
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let vf: setvar f
  let vi: setvar i
  let vp: setvar p
  assume tglng.p: |- P = ( Base ` G )
  assume tglng.l: |- L = ( LineG ` G )
  assume tglng.i: |- I = ( Itv ` G )

  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint f i
  disjoint f p
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint i p
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint G i
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint G p
  disjoint I f
  disjoint I i
  disjoint I p
  disjoint P f
  disjoint P i
  disjoint P p
  assert |- ( G e. TarskiG -> L = ( x e. P , y e. ( P \ { x } ) |-> { z e. P | ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) ) } ) )

  proof
    cG
    cstrkg
    wcel
    cG
    vf
    cv
    #
    clng
    cfv
    vx
    vy
    vp
    cv
    #
    @1
    vx
    cv
    #
    csn
    #
    cdif
    vz
    cv
    #
    @2
    vy
    cv
    #
    vi
    cv
    #
    co
    wcel
    @2
    @4
    @5
    @6
    co
    wcel
    @5
    @2
    @4
    @6
    co
    wcel
    w3o
    vz
    @1
    crab
    cmpt2
    wceq
    vi
    @0
    citv
    cfv
    wsbc
    vp
    @0
    cbs
    cfv
    wsbc
    vf
    cab
    #
    wcel
    #
    cL
    vx
    vy
    cP
    cP
    @3
    cdif
    @4
    @2
    @5
    cI
    co
    wcel
    @2
    @4
    @5
    cI
    co
    wcel
    @5
    @2
    @4
    cI
    co
    wcel
    w3o
    vz
    cP
    crab
    cmpt2
    #
    wceq
    cstrkg
    @7
    cG
    cstrkg
    cstrkgc
    cstrkgb
    cin
    #
    cstrkgcb
    @7
    cin
    #
    cin
    #
    @7
    vx
    vy
    vz
    vf
    vi
    vp
    df-trkg
    @12
    @11
    @7
    @10
    @11
    inss2
    cstrkgcb
    @7
    inss2
    sstri
    eqsstri
    sseli
    @8
    cL
    cG
    clng
    cfv
    #
    @9
    tglng.l
    @8
    cG
    cvv
    wcel
    @13
    @9
    wceq
    vx
    vy
    vz
    cP
    vf
    vi
    cG
    cI
    cG
    cds
    cfv
    #
    vp
    tglng.p
    @14
    eqid
    tglng.i
    istrkgl
    simprbi
    syl5eq
    syl
end
