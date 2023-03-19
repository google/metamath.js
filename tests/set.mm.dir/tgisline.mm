include "cv.mm"
include "co.mm"
include "wcel.mm"
include "w3o.mm"
include "crab.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "cstrkg.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "eldifad.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simprd.mm"
include "necomd.mm"
include "tglngval.mm"
include "jca.mm"
include "ralrimivva.mm"
include "cmpt2.mm"
include "crn.mm"
include "tglng.mm"
include "syl.mm"
include "rneqd.mm"
include "eleqtrd.mm"
include "wb.mm"
include "eqid.mm"
include "elrnmpt2g.mm"
include "mpbid.mm"
include "r19.29d2r.mm"
include "wss.mm"
include "difss.mm"
include "simpr.mm"
include "simpll.mm"
include "eqtr4d.mm"
include "simplr.mm"
include "reximi.mm"
include "ssrexv.mm"
include "mpsyl.mm"

theorem tgisline
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cG: class G
  let cI: class I
  let cL: class L
  let vz: setvar z
  assume tglineelsb2.p: |- B = ( Base ` G )
  assume tglineelsb2.i: |- I = ( Itv ` G )
  assume tglineelsb2.l: |- L = ( LineG ` G )
  assume tglineelsb2.g: |- ( ph -> G e. TarskiG )
  assume tgisline.1: |- ( ph -> A e. ran L )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint G x
  disjoint G y
  disjoint I x
  disjoint I y
  disjoint ph x
  disjoint ph y
  disjoint B z
  disjoint x z
  disjoint y z
  disjoint G z
  disjoint I z
  disjoint ph z
  assert |- ( ph -> E. x e. B E. y e. B ( A = ( x L y ) /\ x =/= y ) )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cL
    co
    #
    vz
    cv
    #
    @0
    @1
    cI
    co
    wcel
    @0
    @3
    @1
    cI
    co
    wcel
    @1
    @0
    @3
    cI
    co
    wcel
    w3o
    vz
    cB
    crab
    #
    wceq
    #
    @0
    @1
    wne
    #
    wa
    #
    cA
    @4
    wceq
    #
    wa
    #
    vy
    cB
    @0
    csn
    #
    cdif
    #
    wrex
    #
    vx
    cB
    wrex
    cA
    @2
    wceq
    #
    @6
    wa
    #
    vy
    cB
    wrex
    #
    vx
    cB
    wrex
    wph
    @7
    @8
    vx
    vy
    cB
    @11
    wph
    @7
    vx
    vy
    cB
    @11
    wph
    @0
    cB
    wcel
    #
    @1
    @11
    wcel
    #
    wa
    #
    wa
    #
    @5
    @6
    @19
    vz
    cB
    cG
    cI
    cL
    @0
    @1
    tglineelsb2.p
    tglineelsb2.l
    tglineelsb2.i
    wph
    cG
    cstrkg
    wcel
    #
    @18
    tglineelsb2.g
    adantr
    wph
    @16
    @17
    simprl
    @19
    @1
    cB
    @10
    wph
    @16
    @17
    simprr
    #
    eldifad
    @19
    @1
    @0
    @19
    @1
    cB
    wcel
    #
    @1
    @0
    wne
    #
    @19
    @17
    @22
    @23
    wa
    @21
    @1
    cB
    @0
    eldifsn
    sylib
    simprd
    necomd
    #
    tglngval
    @24
    jca
    ralrimivva
    wph
    cA
    vx
    vy
    cB
    @11
    @4
    cmpt2
    #
    crn
    #
    wcel
    #
    @8
    vy
    @11
    wrex
    vx
    cB
    wrex
    #
    wph
    cA
    cL
    crn
    #
    @26
    tgisline.1
    wph
    cL
    @25
    wph
    @20
    cL
    @25
    wceq
    tglineelsb2.g
    vx
    vy
    vz
    cB
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.l
    tglineelsb2.i
    tglng
    syl
    rneqd
    eleqtrd
    wph
    cA
    @29
    wcel
    @27
    @28
    wb
    tgisline.1
    vx
    vy
    cB
    @11
    @4
    cA
    @25
    @29
    @25
    eqid
    elrnmpt2g
    syl
    mpbid
    r19.29d2r
    @12
    @15
    vx
    cB
    @11
    cB
    wss
    @12
    @14
    vy
    @11
    wrex
    @15
    cB
    @10
    difss
    @9
    @14
    vy
    @11
    @9
    @13
    @6
    @9
    cA
    @4
    @2
    @7
    @8
    simpr
    @5
    @6
    @8
    simpll
    eqtr4d
    @5
    @6
    @8
    simplr
    jca
    reximi
    @14
    vy
    @11
    cB
    ssrexv
    mpsyl
    reximi
    syl
end
