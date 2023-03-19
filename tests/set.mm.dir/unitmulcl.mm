include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cur.mm"
include "cfv.mm"
include "cdsr.mm"
include "wbr.mm"
include "coppr.mm"
include "simp1.mm"
include "cbs.mm"
include "simp3.mm"
include "eqid.mm"
include "unitcl.mm"
include "syl.mm"
include "wa.mm"
include "simp2.mm"
include "isunit.mm"
include "sylib.mm"
include "simpld.mm"
include "dvdsrmul1.mm"
include "syl3anc.mm"
include "wceq.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "breqtrd.mm"
include "dvdsrtr.mm"
include "opprring.mm"
include "cmulr.mm"
include "opprmul.mm"
include "simprd.mm"
include "opprbas.mm"
include "ringridm.mm"
include "syl5eq.mm"
include "syl5eqbrr.mm"
include "sylanbrc.mm"

theorem unitmulcl
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cX: class X
  let cY: class Y
  assume unitmulcl.1: |- U = ( Unit ` R )
  assume unitmulcl.2: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ X e. U /\ Y e. U ) -> ( X .x. Y ) e. U )

  proof
    cR
    crg
    wcel
    #
    cX
    cU
    wcel
    #
    cY
    cU
    wcel
    #
    w3a
    #
    cX
    cY
    c.x
    co
    #
    cR
    cur
    cfv
    #
    cR
    cdsr
    cfv
    #
    wbr
    #
    @4
    @5
    cR
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    #
    @4
    cU
    wcel
    @3
    @0
    @4
    cY
    @6
    wbr
    cY
    @5
    @6
    wbr
    #
    @7
    @0
    @1
    @2
    simp1
    #
    @3
    @4
    @5
    cY
    c.x
    co
    #
    cY
    @6
    @3
    @0
    cY
    cR
    cbs
    cfv
    #
    wcel
    #
    cX
    @5
    @6
    wbr
    #
    @4
    @13
    @6
    wbr
    @12
    @3
    @2
    @15
    @0
    @1
    @2
    simp3
    #
    @14
    cR
    cU
    cY
    @14
    eqid
    #
    unitmulcl.1
    unitcl
    syl
    #
    @3
    @16
    cX
    @5
    @9
    wbr
    #
    @3
    @1
    @16
    @20
    wa
    @0
    @1
    @2
    simp2
    #
    @6
    cR
    @8
    cU
    @5
    @9
    cX
    unitmulcl.1
    @5
    eqid
    #
    @6
    eqid
    #
    @8
    eqid
    #
    @9
    eqid
    #
    isunit
    sylib
    #
    simpld
    @14
    @6
    cR
    c.x
    cX
    @5
    cY
    @18
    @23
    unitmulcl.2
    dvdsrmul1
    syl3anc
    @3
    @0
    @15
    @13
    cY
    wceq
    @12
    @19
    @14
    cR
    c.x
    @5
    cY
    @18
    unitmulcl.2
    @22
    ringlidm
    syl2anc
    breqtrd
    @3
    @11
    cY
    @5
    @9
    wbr
    #
    @3
    @2
    @11
    @27
    wa
    @17
    @6
    cR
    @8
    cU
    @5
    @9
    cY
    unitmulcl.1
    @22
    @23
    @24
    @25
    isunit
    sylib
    #
    simpld
    @14
    @6
    cR
    @5
    @4
    cY
    @18
    @23
    dvdsrtr
    syl3anc
    @3
    @8
    crg
    wcel
    #
    @4
    cX
    @9
    wbr
    @20
    @10
    @3
    @0
    @29
    @12
    cR
    @8
    @24
    opprring
    syl
    #
    @3
    @4
    cY
    cX
    @8
    cmulr
    cfv
    #
    co
    #
    cX
    @9
    @14
    cR
    @31
    c.x
    @8
    cY
    cX
    @18
    unitmulcl.2
    @24
    @31
    eqid
    #
    opprmul
    @3
    @32
    @5
    cX
    @31
    co
    #
    cX
    @9
    @3
    @29
    cX
    @14
    wcel
    #
    @27
    @32
    @34
    @9
    wbr
    @30
    @3
    @1
    @35
    @21
    @14
    cR
    cU
    cX
    @18
    unitmulcl.1
    unitcl
    syl
    #
    @3
    @11
    @27
    @28
    simprd
    @14
    @9
    @8
    @31
    cY
    @5
    cX
    @14
    cR
    @8
    @24
    @18
    opprbas
    #
    @25
    @33
    dvdsrmul1
    syl3anc
    @3
    @34
    cX
    @5
    c.x
    co
    #
    cX
    @14
    cR
    @31
    c.x
    @8
    @5
    cX
    @18
    unitmulcl.2
    @24
    @33
    opprmul
    @3
    @0
    @35
    @38
    cX
    wceq
    @12
    @36
    @14
    cR
    c.x
    @5
    cX
    @18
    unitmulcl.2
    @22
    ringridm
    syl2anc
    syl5eq
    breqtrd
    syl5eqbrr
    @3
    @16
    @20
    @26
    simprd
    @14
    @9
    @8
    @5
    @4
    cX
    @37
    @25
    dvdsrtr
    syl3anc
    @6
    cR
    @8
    cU
    @5
    @9
    @4
    unitmulcl.1
    @22
    @23
    @24
    @25
    isunit
    sylanbrc
end
