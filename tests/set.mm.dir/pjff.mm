include "cphl.mm"
include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "cocv.mm"
include "cfv.mm"
include "cpj1.mm"
include "co.mm"
include "clmhm.mm"
include "wa.mm"
include "clsm.mm"
include "cress.mm"
include "clss.mm"
include "c0g.mm"
include "eqid.mm"
include "clmod.mm"
include "phllmod.mm"
include "adantr.mm"
include "cbs.mm"
include "wceq.mm"
include "pjdm2.mm"
include "simprbda.mm"
include "wss.mm"
include "lssss.mm"
include "syl.mm"
include "ocvlss.mm"
include "syldan.mm"
include "cin.mm"
include "csn.mm"
include "ocvin.mm"
include "pj1lmhm.mm"
include "simplbda.mm"
include "oveq2d.mm"
include "ressid.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "pjfval2.mm"
include "fmptd.mm"

theorem pjff
  let cK: class K
  let cW: class W
  let vx: setvar x
  let cT: class T
  assume pjf.k: |- K = ( proj ` W )


  assert |- ( W e. PreHil -> K : dom K --> ( W LMHom W ) )

  proof
    cW
    cphl
    wcel
    #
    vx
    cK
    cdm
    #
    vx
    cv
    #
    @2
    cW
    cocv
    cfv
    #
    cfv
    #
    cW
    cpj1
    cfv
    #
    co
    #
    cW
    cW
    clmhm
    co
    #
    cK
    @0
    @2
    @1
    wcel
    #
    wa
    #
    @6
    cW
    @2
    @4
    cW
    clsm
    cfv
    #
    co
    #
    cress
    co
    #
    cW
    clmhm
    co
    @7
    @9
    @5
    @10
    @2
    @4
    cW
    clss
    cfv
    #
    cW
    cW
    c0g
    cfv
    #
    @13
    eqid
    #
    @10
    eqid
    #
    @14
    eqid
    #
    @5
    eqid
    #
    @0
    cW
    clmod
    wcel
    @8
    cW
    phllmod
    adantr
    @0
    @8
    @2
    @13
    wcel
    #
    @11
    cW
    cbs
    cfv
    #
    wceq
    #
    @10
    @2
    cK
    @13
    @3
    @20
    cW
    @20
    eqid
    #
    @15
    @3
    eqid
    #
    @16
    pjf.k
    pjdm2
    #
    simprbda
    #
    @0
    @8
    @2
    @20
    wss
    #
    @4
    @13
    wcel
    @9
    @19
    @26
    @25
    @13
    @2
    @20
    cW
    @22
    @15
    lssss
    syl
    @2
    @13
    @3
    @20
    cW
    @22
    @23
    @15
    ocvlss
    syldan
    @0
    @8
    @19
    @2
    @4
    cin
    @14
    csn
    wceq
    @25
    @2
    @13
    @3
    cW
    @14
    @23
    @15
    @17
    ocvin
    syldan
    pj1lmhm
    @9
    @12
    cW
    cW
    clmhm
    @9
    @12
    cW
    @20
    cress
    co
    #
    cW
    @9
    @11
    @20
    cW
    cress
    @0
    @8
    @19
    @21
    @24
    simplbda
    oveq2d
    @0
    @27
    cW
    wceq
    @8
    @20
    cW
    cphl
    @22
    ressid
    adantr
    eqtrd
    oveq1d
    eleqtrd
    vx
    @5
    cK
    @3
    cW
    @23
    @18
    pjf.k
    pjfval2
    fmptd
end
