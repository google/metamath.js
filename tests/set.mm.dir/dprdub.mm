include "cfv.mm"
include "cdprd.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "c0g.mm"
include "cif.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cixp.mm"
include "crab.mm"
include "eqid.mm"
include "cdm.mm"
include "adantr.mm"
include "simpr.mm"
include "dprdfid.mm"
include "simprd.mm"
include "simpld.mm"
include "eldprdi.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"

theorem dprdub
  let wph: wff ph
  let cS: class S
  let cG: class G
  let cI: class I
  let cX: class X
  let vh: setvar h
  let vi: setvar i
  let vn: setvar n
  let vx: setvar x
  assume dprdub.1: |- ( ph -> G dom DProd S )
  assume dprdub.2: |- ( ph -> dom S = I )
  assume dprdub.3: |- ( ph -> X e. I )


  assert |- ( ph -> ( S ` X ) C_ ( G DProd S ) )

  proof
    wph
    vx
    cX
    cS
    cfv
    #
    cG
    cS
    cdprd
    co
    #
    wph
    vx
    cv
    #
    @0
    wcel
    #
    @2
    @1
    wcel
    wph
    @3
    wa
    #
    cG
    vn
    cI
    vn
    cv
    cX
    wceq
    @2
    cG
    c0g
    cfv
    #
    cif
    cmpt
    #
    cgsu
    co
    #
    @2
    @1
    @4
    @6
    vh
    cv
    @5
    cfsupp
    wbr
    vh
    vi
    cI
    vi
    cv
    cS
    cfv
    cixp
    crab
    #
    wcel
    #
    @7
    @2
    wceq
    #
    @4
    @2
    cS
    vh
    vi
    vn
    @6
    cG
    cI
    @8
    cX
    @5
    @5
    eqid
    #
    @8
    eqid
    #
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    @3
    dprdub.1
    adantr
    #
    wph
    cS
    cdm
    cI
    wceq
    @3
    dprdub.2
    adantr
    #
    wph
    cX
    cI
    wcel
    @3
    dprdub.3
    adantr
    wph
    @3
    simpr
    @6
    eqid
    dprdfid
    #
    simprd
    @4
    cS
    vh
    vi
    @6
    cG
    cI
    @8
    @5
    @11
    @12
    @13
    @14
    @4
    @9
    @10
    @15
    simpld
    eldprdi
    eqeltrrd
    ex
    ssrdv
end
