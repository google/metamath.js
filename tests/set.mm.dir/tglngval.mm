include "co.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "w3o.mm"
include "crab.mm"
include "cmpt2.mm"
include "cstrkg.mm"
include "wceq.mm"
include "tglng.mm"
include "syl.mm"
include "oveqd.mm"
include "cvv.mm"
include "wne.mm"
include "necomd.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "a1i.mm"
include "wa.mm"
include "oveq12.mm"
include "eleq2d.mm"
include "simpl.mm"
include "simpr.mm"
include "oveq2d.mm"
include "eleq12d.mm"
include "oveq1d.mm"
include "3orbi123d.mm"
include "rabbidv.mm"
include "sneq.mm"
include "difeq2d.mm"
include "eqid.mm"
include "ovmpt2x.mm"
include "syl3anc.mm"
include "eqtrd.mm"

theorem tglngval
  let wph: wff ph
  let vz: setvar z
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume tglngval.p: |- P = ( Base ` G )
  assume tglngval.l: |- L = ( LineG ` G )
  assume tglngval.i: |- I = ( Itv ` G )
  assume tglngval.g: |- ( ph -> G e. TarskiG )
  assume tglngval.x: |- ( ph -> X e. P )
  assume tglngval.y: |- ( ph -> Y e. P )
  assume tglngval.z: |- ( ph -> X =/= Y )

  disjoint G z
  disjoint I z
  disjoint P z
  disjoint X z
  disjoint Y z
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint I x
  disjoint I y
  disjoint P x
  disjoint P y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( X L Y ) = { z e. P | ( z e. ( X I Y ) \/ X e. ( z I Y ) \/ Y e. ( X I z ) ) } )

  proof
    wph
    cX
    cY
    cL
    co
    cX
    cY
    vx
    vy
    cP
    cP
    vx
    cv
    #
    csn
    #
    cdif
    #
    vz
    cv
    #
    @0
    vy
    cv
    #
    cI
    co
    #
    wcel
    #
    @0
    @3
    @4
    cI
    co
    #
    wcel
    #
    @4
    @0
    @3
    cI
    co
    #
    wcel
    #
    w3o
    #
    vz
    cP
    crab
    #
    cmpt2
    #
    co
    #
    @3
    cX
    cY
    cI
    co
    #
    wcel
    #
    cX
    @3
    cY
    cI
    co
    #
    wcel
    #
    cY
    cX
    @3
    cI
    co
    #
    wcel
    #
    w3o
    #
    vz
    cP
    crab
    #
    wph
    cL
    @13
    cX
    cY
    wph
    cG
    cstrkg
    wcel
    cL
    @13
    wceq
    tglngval.g
    vx
    vy
    vz
    cP
    cG
    cI
    cL
    tglngval.p
    tglngval.l
    tglngval.i
    tglng
    syl
    oveqd
    wph
    cX
    cP
    wcel
    cY
    cP
    cX
    csn
    #
    cdif
    #
    wcel
    #
    @22
    cvv
    wcel
    #
    @14
    @22
    wceq
    tglngval.x
    wph
    cY
    cP
    wcel
    cY
    cX
    wne
    @25
    tglngval.y
    wph
    cX
    cY
    tglngval.z
    necomd
    cY
    cP
    cX
    eldifsn
    sylanbrc
    @26
    wph
    @21
    vz
    cP
    cP
    cG
    cbs
    cfv
    cvv
    tglngval.p
    cG
    cbs
    fvex
    eqeltri
    rabex
    a1i
    vx
    vy
    cX
    cY
    cP
    @2
    @12
    @22
    @13
    cvv
    @24
    @0
    cX
    wceq
    #
    @4
    cY
    wceq
    #
    wa
    #
    @11
    @21
    vz
    cP
    @29
    @6
    @16
    @8
    @18
    @10
    @20
    @29
    @5
    @15
    @3
    @0
    cX
    @4
    cY
    cI
    oveq12
    eleq2d
    @29
    @0
    cX
    @7
    @17
    @27
    @28
    simpl
    #
    @29
    @4
    cY
    @3
    cI
    @27
    @28
    simpr
    #
    oveq2d
    eleq12d
    @29
    @4
    cY
    @9
    @19
    @31
    @29
    @0
    cX
    @3
    cI
    @30
    oveq1d
    eleq12d
    3orbi123d
    rabbidv
    @27
    @1
    @23
    cP
    @0
    cX
    sneq
    difeq2d
    @13
    eqid
    ovmpt2x
    syl3anc
    eqtrd
end
