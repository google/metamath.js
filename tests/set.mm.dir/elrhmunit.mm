include "crh.mm"
include "co.mm"
include "wcel.mm"
include "cui.mm"
include "cfv.mm"
include "wa.mm"
include "cur.mm"
include "cdsr.mm"
include "wbr.mm"
include "coppr.mm"
include "cbs.mm"
include "simpl.mm"
include "eqid.mm"
include "unitss.mm"
include "simpr.mm"
include "sseldi.mm"
include "crg.mm"
include "rhmrcl1.mm"
include "ringidcl.mm"
include "3syl.mm"
include "isunit.mm"
include "sylib.mm"
include "simpld.mm"
include "rhmdvdsr.mm"
include "syl31anc.mm"
include "wb.mm"
include "rhm1.mm"
include "breq2d.mm"
include "adantr.mm"
include "mpbid.mm"
include "rhmopp.mm"
include "simprd.mm"
include "opprbas.mm"
include "sylanbrc.mm"

theorem elrhmunit
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( ( F e. ( R RingHom S ) /\ A e. ( Unit ` R ) ) -> ( F ` A ) e. ( Unit ` S ) )

  proof
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cA
    cR
    cui
    cfv
    #
    wcel
    #
    wa
    #
    cA
    cF
    cfv
    #
    cS
    cur
    cfv
    #
    cS
    cdsr
    cfv
    #
    wbr
    #
    @4
    @5
    cS
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    #
    @4
    cS
    cui
    cfv
    #
    wcel
    @3
    @4
    cR
    cur
    cfv
    #
    cF
    cfv
    #
    @6
    wbr
    #
    @7
    @3
    @0
    cA
    cR
    cbs
    cfv
    #
    wcel
    #
    @12
    @15
    wcel
    #
    cA
    @12
    cR
    cdsr
    cfv
    #
    wbr
    #
    @14
    @0
    @2
    simpl
    #
    @3
    @1
    @15
    cA
    @15
    cR
    @1
    @15
    eqid
    #
    @1
    eqid
    #
    unitss
    @0
    @2
    simpr
    #
    sseldi
    #
    @3
    @0
    cR
    crg
    wcel
    @17
    @20
    cR
    cS
    cF
    rhmrcl1
    @15
    cR
    @12
    @21
    @12
    eqid
    #
    ringidcl
    3syl
    #
    @3
    @19
    cA
    @12
    cR
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    #
    @3
    @2
    @19
    @29
    wa
    @23
    @18
    cR
    @27
    @1
    @12
    @28
    cA
    @22
    @25
    @18
    eqid
    #
    @27
    eqid
    #
    @28
    eqid
    #
    isunit
    sylib
    #
    simpld
    cA
    @12
    @18
    @6
    cR
    cS
    cF
    @15
    @21
    @30
    @6
    eqid
    #
    rhmdvdsr
    syl31anc
    @0
    @14
    @7
    wb
    @2
    @0
    @13
    @5
    @4
    @6
    cR
    cS
    @12
    cF
    @5
    @25
    @5
    eqid
    #
    rhm1
    #
    breq2d
    adantr
    mpbid
    @3
    @4
    @13
    @9
    wbr
    #
    @10
    @3
    cF
    @27
    @8
    crh
    co
    wcel
    #
    @16
    @17
    @29
    @37
    @0
    @38
    @2
    cR
    cS
    cF
    rhmopp
    adantr
    @24
    @26
    @3
    @19
    @29
    @33
    simprd
    cA
    @12
    @28
    @9
    @27
    @8
    cF
    @15
    @15
    cR
    @27
    @31
    @21
    opprbas
    @32
    @9
    eqid
    #
    rhmdvdsr
    syl31anc
    @0
    @37
    @10
    wb
    @2
    @0
    @13
    @5
    @4
    @9
    @36
    breq2d
    adantr
    mpbid
    @6
    cS
    @8
    @11
    @5
    @9
    @4
    @11
    eqid
    @35
    @34
    @8
    eqid
    @39
    isunit
    sylanbrc
end
