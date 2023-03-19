include "cli.mm"
include "wbr.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "clm.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cz.mm"
include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "wb.mm"
include "cr.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "fssd.mm"
include "eqid.mm"
include "lmclimf.mm"
include "syl2anc.mm"
include "wa.mm"
include "cvv.mm"
include "tgioo2.mm"
include "reex.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "simpr.mm"
include "adantr.mm"
include "lmss.mm"
include "pm5.32da.mm"
include "biimpa.mm"
include "cv.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "climrecl.mm"
include "ex.mm"
include "ancrd.mm"
include "impbid2.mm"
include "ctopon.mm"
include "retopon.mm"
include "lmcl.mm"
include "3bitr3d.mm"
include "bitr3d.mm"
include "breqi.mm"
include "syl6rbbr.mm"

theorem climreeq
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vn: setvar n
  assume climreeq.1: |- R = ( ~~>t ` ( topGen ` ran (,) ) )
  assume climreeq.2: |- Z = ( ZZ>= ` M )
  assume climreeq.3: |- ( ph -> M e. ZZ )
  assume climreeq.4: |- ( ph -> F : Z --> RR )


  assert |- ( ph -> ( F R A <-> F ~~> A ) )

  proof
    wph
    cF
    cA
    cli
    wbr
    #
    cF
    cA
    cioo
    crn
    ctg
    cfv
    #
    clm
    cfv
    #
    wbr
    #
    cF
    cA
    cR
    wbr
    wph
    cF
    cA
    ccnfld
    ctopn
    cfv
    #
    clm
    cfv
    wbr
    #
    @0
    @3
    wph
    cM
    cz
    wcel
    #
    cZ
    cc
    cF
    wf
    @5
    @0
    wb
    climreeq.3
    wph
    cZ
    cr
    cc
    cF
    climreeq.4
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    fssd
    cA
    cF
    @4
    cM
    cZ
    @4
    eqid
    #
    climreeq.2
    lmclimf
    syl2anc
    #
    wph
    cA
    cr
    wcel
    #
    @5
    wa
    #
    @9
    @3
    wa
    #
    @5
    @3
    wph
    @9
    @5
    @3
    wph
    @9
    wa
    #
    cA
    cF
    @4
    @1
    cM
    cvv
    cr
    cZ
    @4
    @7
    tgioo2
    climreeq.2
    cr
    cvv
    wcel
    @12
    reex
    a1i
    @4
    ctop
    wcel
    @12
    @4
    @7
    cnfldtop
    a1i
    wph
    @9
    simpr
    wph
    @6
    @9
    climreeq.3
    adantr
    wph
    cZ
    cr
    cF
    wf
    @9
    climreeq.4
    adantr
    lmss
    pm5.32da
    wph
    @10
    @5
    @9
    @5
    simpr
    wph
    @5
    @9
    wph
    @5
    @9
    wph
    @5
    wa
    cA
    vn
    cF
    cM
    cZ
    climreeq.2
    wph
    @6
    @5
    climreeq.3
    adantr
    wph
    @5
    @0
    @8
    biimpa
    wph
    vn
    cv
    #
    cZ
    wcel
    @13
    cF
    cfv
    cr
    wcel
    @5
    wph
    cZ
    cr
    @13
    cF
    climreeq.4
    ffvelrnda
    adantlr
    climrecl
    ex
    ancrd
    impbid2
    wph
    @11
    @3
    @9
    @3
    simpr
    wph
    @3
    @9
    wph
    @3
    @9
    wph
    @3
    wa
    #
    @1
    cr
    ctopon
    cfv
    wcel
    #
    @3
    @9
    @15
    @14
    retopon
    a1i
    wph
    @3
    simpr
    cA
    cF
    @1
    cr
    lmcl
    syl2anc
    ex
    ancrd
    impbid2
    3bitr3d
    bitr3d
    cF
    cA
    cR
    @2
    climreeq.1
    breqi
    syl6rbbr
end
