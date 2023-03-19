include "cz.mm"
include "wrex.mm"
include "wo.mm"
include "cn0.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cr.mm"
include "elznn0.mm"
include "simprbi.mm"
include "adantr.mm"
include "simpr.mm"
include "simplr.mm"
include "wceq.mm"
include "wb.mm"
include "equcoms.mm"
include "bicomd.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "zcn.mm"
include "negnegd.mm"
include "eqcomd.mm"
include "negeq.mm"
include "eqeq2d.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "syl.mm"
include "adantlr.mm"
include "rspcedv.mm"
include "impancom.mm"
include "orim12d.mm"
include "mpd.mm"
include "r19.43.mm"
include "sylibr.mm"
include "rexlimiva.mm"
include "nn0z.mm"
include "sylan.mm"
include "nn0negz.mm"
include "jaodan.mm"
include "impbii.mm"

theorem rexzrexnn0
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  assume rexzrexnn0.1: |- ( x = y -> ( ph <-> ps ) )
  assume rexzrexnn0.2: |- ( x = -u y -> ( ph <-> ch ) )

  disjoint ph y
  disjoint ps x
  disjoint ch x
  disjoint x y
  assert |- ( E. x e. ZZ ph <-> E. y e. NN0 ( ps \/ ch ) )

  proof
    wph
    vx
    cz
    wrex
    #
    wps
    wch
    wo
    #
    vy
    cn0
    wrex
    #
    wph
    @2
    vx
    cz
    vx
    cv
    #
    cz
    wcel
    #
    wph
    wa
    #
    wps
    vy
    cn0
    wrex
    #
    wch
    vy
    cn0
    wrex
    #
    wo
    #
    @2
    @5
    @3
    cn0
    wcel
    #
    @3
    cneg
    #
    cn0
    wcel
    #
    wo
    #
    @8
    @4
    @12
    wph
    @4
    @3
    cr
    wcel
    @12
    @3
    elznn0
    simprbi
    adantr
    @5
    @9
    @6
    @11
    @7
    @5
    @9
    @6
    @5
    @9
    wa
    @9
    wph
    @6
    @5
    @9
    simpr
    @4
    wph
    @9
    simplr
    wps
    wph
    vy
    @3
    cn0
    vy
    cv
    #
    @3
    wceq
    wph
    wps
    wph
    wps
    wb
    vx
    vy
    rexzrexnn0.1
    equcoms
    bicomd
    rspcev
    syl2anc
    ex
    @4
    @11
    wph
    @7
    @4
    @11
    wa
    wch
    wph
    vy
    @10
    cn0
    @4
    @11
    simpr
    @4
    @13
    @10
    wceq
    #
    wch
    wph
    wb
    @11
    @4
    @14
    wa
    #
    wph
    wch
    @15
    @3
    @13
    cneg
    #
    wceq
    #
    wph
    wch
    wb
    @4
    @14
    @17
    @4
    @17
    @14
    @3
    @10
    cneg
    #
    wceq
    @4
    @18
    @3
    @4
    @3
    @3
    zcn
    negnegd
    eqcomd
    @14
    @16
    @18
    @3
    @13
    @10
    negeq
    eqeq2d
    syl5ibrcom
    imp
    rexzrexnn0.2
    syl
    bicomd
    adantlr
    rspcedv
    impancom
    orim12d
    mpd
    wps
    wch
    vy
    cn0
    r19.43
    sylibr
    rexlimiva
    @1
    @0
    vy
    cn0
    @13
    cn0
    wcel
    #
    wps
    @0
    wch
    @19
    @13
    cz
    wcel
    wps
    @0
    @13
    nn0z
    wph
    wps
    vx
    @13
    cz
    rexzrexnn0.1
    rspcev
    sylan
    @19
    @16
    cz
    wcel
    wch
    @0
    @13
    nn0negz
    wph
    wch
    vx
    @16
    cz
    rexzrexnn0.2
    rspcev
    sylan
    jaodan
    rexlimiva
    impbii
end
