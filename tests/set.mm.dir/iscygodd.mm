include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "cv.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "ccyg.mm"
include "chash.mm"
include "cfn.mm"
include "wa.mm"
include "wb.mm"
include "cn0.mm"
include "odcl.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "hashclb.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "eqid.mm"
include "cyggenod.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "ne0i.mm"
include "iscyg2.mm"
include "sylanbrc.mm"

theorem iscygodd
  let wph: wff ph
  let cB: class B
  let cG: class G
  let cO: class O
  let cX: class X
  let vn: setvar n
  let vx: setvar x
  assume iscygodd.1: |- B = ( Base ` G )
  assume iscygodd.o: |- O = ( od ` G )
  assume iscygodd.3: |- ( ph -> G e. Grp )
  assume iscygodd.4: |- ( ph -> X e. B )
  assume iscygodd.5: |- ( ph -> ( O ` X ) = ( # ` B ) )


  assert |- ( ph -> G e. CycGrp )

  proof
    wph
    cG
    cgrp
    wcel
    #
    vn
    cz
    vn
    cv
    vx
    cv
    cG
    cmg
    cfv
    #
    co
    cmpt
    crn
    cB
    wceq
    vx
    cB
    crab
    #
    c0
    wne
    #
    cG
    ccyg
    wcel
    iscygodd.3
    wph
    cX
    @2
    wcel
    #
    @3
    wph
    @4
    cX
    cB
    wcel
    #
    cX
    cO
    cfv
    #
    cB
    chash
    cfv
    #
    wceq
    #
    iscygodd.4
    iscygodd.5
    wph
    @0
    cB
    cfn
    wcel
    #
    @4
    @5
    @8
    wa
    wb
    iscygodd.3
    wph
    @7
    cn0
    wcel
    #
    @9
    wph
    @6
    @7
    cn0
    iscygodd.5
    wph
    @5
    @6
    cn0
    wcel
    iscygodd.4
    cX
    cG
    cO
    cB
    iscygodd.1
    iscygodd.o
    odcl
    syl
    eqeltrrd
    cB
    cvv
    wcel
    @9
    @10
    wb
    cB
    cG
    cbs
    cfv
    cvv
    iscygodd.1
    cG
    cbs
    fvex
    eqeltri
    cB
    cvv
    hashclb
    ax-mp
    sylibr
    vx
    cB
    @1
    vn
    @2
    cG
    cO
    cX
    iscygodd.1
    @1
    eqid
    #
    @2
    eqid
    #
    iscygodd.o
    cyggenod
    syl2anc
    mpbir2and
    @2
    cX
    ne0i
    syl
    vx
    cB
    @1
    vn
    @2
    cG
    iscygodd.1
    @11
    @12
    iscyg2
    sylanbrc
end
