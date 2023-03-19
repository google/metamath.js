include "cc0.mm"
include "c1.mm"
include "cico.mm"
include "co.mm"
include "cpnf.mm"
include "wf1o.mm"
include "ccnv.mm"
include "cv.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "wtru.mm"
include "cmin.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0re.mm"
include "1re.mm"
include "rexri.mm"
include "elico2.mm"
include "mp2an.mm"
include "simp1bi.mm"
include "crp.mm"
include "simp3bi.mm"
include "difrp.mm"
include "sylancl.mm"
include "mpbid.mm"
include "rerpdivcld.mm"
include "simp2bi.mm"
include "divge0d.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "adantl.mm"
include "simplbi.mm"
include "readdcl.mm"
include "sylancr.mm"
include "a1i.mm"
include "simprbi.mm"
include "ltp1d.mm"
include "cc.mm"
include "ax-1cn.mm"
include "recnd.mm"
include "addcom.mm"
include "breqtrrd.mm"
include "lelttrd.mm"
include "elrpd.mm"
include "divge0.mm"
include "syl22anc.mm"
include "cmul.mm"
include "mulid1d.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "syl3anbrc.mm"
include "adantr.mm"
include "mulcld.mm"
include "subadd2d.mm"
include "1cnd.mm"
include "subdird.mm"
include "mulid2d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "adddid.mm"
include "3bitr4rd.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "rpne0d.mm"
include "divmul3d.mm"
include "rpcnd.mm"
include "divmul2d.mm"
include "3bitr4d.mm"
include "f1ocnv2d.mm"
include "trud.mm"

theorem icopnfcnv
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cA: class A
  let cB: class B
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cG: class G
  let cJ: class J
  assume icopnfhmeo.f: |- F = ( x e. ( 0 [,) 1 ) |-> ( x / ( 1 - x ) ) )

  disjoint x y
  disjoint F y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint y z
  disjoint F z
  disjoint G w
  disjoint G z
  disjoint v x
  disjoint J v
  disjoint w x
  disjoint J w
  disjoint x z
  disjoint J x
  disjoint J y
  disjoint J z
  assert |- ( F : ( 0 [,) 1 ) -1-1-onto-> ( 0 [,) +oo ) /\ `' F = ( y e. ( 0 [,) +oo ) |-> ( y / ( 1 + y ) ) ) )

  proof
    cc0
    c1
    cico
    co
    #
    cc0
    cpnf
    cico
    co
    #
    cF
    wf1o
    cF
    ccnv
    vy
    @1
    vy
    cv
    #
    c1
    @2
    caddc
    co
    #
    cdiv
    co
    #
    cmpt
    wceq
    wa
    wtru
    vx
    vy
    @0
    @1
    vx
    cv
    #
    c1
    @5
    cmin
    co
    #
    cdiv
    co
    #
    @4
    cF
    icopnfhmeo.f
    @5
    @0
    wcel
    #
    @7
    @1
    wcel
    #
    wtru
    @8
    @7
    cr
    wcel
    cc0
    @7
    cle
    wbr
    @9
    @8
    @5
    @6
    @8
    @5
    cr
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    @5
    c1
    clt
    wbr
    #
    cc0
    cr
    wcel
    #
    c1
    cxr
    wcel
    #
    @8
    @10
    @11
    @12
    w3a
    wb
    0re
    c1
    1re
    rexri
    #
    cc0
    c1
    @5
    elico2
    mp2an
    #
    simp1bi
    #
    @8
    @12
    @6
    crp
    wcel
    #
    @8
    @10
    @11
    @12
    @16
    simp3bi
    @8
    @10
    c1
    cr
    wcel
    #
    @12
    @18
    wb
    @17
    1re
    @5
    c1
    difrp
    sylancl
    mpbid
    #
    rerpdivcld
    @8
    @5
    @6
    @17
    @20
    @8
    @10
    @11
    @12
    @16
    simp2bi
    divge0d
    @7
    elrege0
    sylanbrc
    adantl
    @2
    @1
    wcel
    #
    @4
    @0
    wcel
    #
    wtru
    @21
    @4
    cr
    wcel
    #
    cc0
    @4
    cle
    wbr
    #
    @4
    c1
    clt
    wbr
    #
    @22
    @21
    @2
    @3
    @21
    @2
    cr
    wcel
    #
    cc0
    @2
    cle
    wbr
    #
    @2
    elrege0
    #
    simplbi
    #
    @21
    @3
    @21
    @19
    @26
    @3
    cr
    wcel
    #
    1re
    @29
    c1
    @2
    readdcl
    sylancr
    #
    @21
    cc0
    @2
    @3
    @13
    @21
    0re
    a1i
    @29
    @31
    @21
    @26
    @27
    @28
    simprbi
    #
    @21
    @2
    @2
    c1
    caddc
    co
    #
    @3
    clt
    @21
    @2
    @29
    ltp1d
    @21
    c1
    cc
    wcel
    @2
    cc
    wcel
    #
    @3
    @33
    wceq
    ax-1cn
    @21
    @2
    @29
    recnd
    #
    c1
    @2
    addcom
    sylancr
    breqtrrd
    #
    lelttrd
    #
    elrpd
    #
    rerpdivcld
    @21
    @26
    @27
    @30
    cc0
    @3
    clt
    wbr
    #
    @24
    @29
    @32
    @31
    @37
    @2
    @3
    divge0
    syl22anc
    @21
    @25
    @2
    @3
    c1
    cmul
    co
    #
    clt
    wbr
    #
    @21
    @2
    @3
    @40
    clt
    @36
    @21
    @3
    @21
    @3
    @31
    recnd
    #
    mulid1d
    breqtrrd
    @21
    @26
    @19
    @30
    @39
    @25
    @41
    wb
    @29
    @19
    @21
    1re
    a1i
    @31
    @37
    @2
    c1
    @3
    ltdivmul
    syl112anc
    mpbird
    @13
    @14
    @22
    @23
    @24
    @25
    w3a
    wb
    0re
    @15
    cc0
    c1
    @4
    elico2
    mp2an
    syl3anbrc
    adantl
    @8
    @21
    wa
    #
    @5
    @4
    wceq
    #
    @2
    @7
    wceq
    #
    wb
    wtru
    @43
    @4
    @5
    wceq
    #
    @7
    @2
    wceq
    #
    @44
    @45
    @43
    @2
    @5
    @3
    cmul
    co
    #
    wceq
    #
    @5
    @6
    @2
    cmul
    co
    #
    wceq
    #
    @46
    @47
    @43
    @48
    @2
    wceq
    #
    @50
    @5
    wceq
    #
    @49
    @51
    @43
    @2
    @5
    @2
    cmul
    co
    #
    cmin
    co
    #
    @5
    wceq
    @5
    @54
    caddc
    co
    #
    @2
    wceq
    @53
    @52
    @43
    @2
    @54
    @5
    @21
    @34
    @8
    @35
    adantl
    #
    @43
    @5
    @2
    @43
    @5
    @8
    @10
    @21
    @17
    adantr
    recnd
    #
    @57
    mulcld
    @58
    subadd2d
    @43
    @50
    @55
    @5
    @43
    @50
    c1
    @2
    cmul
    co
    #
    @54
    cmin
    co
    @55
    @43
    c1
    @5
    @2
    @43
    1cnd
    #
    @58
    @57
    subdird
    @43
    @59
    @2
    @54
    cmin
    @43
    @2
    @57
    mulid2d
    oveq1d
    eqtrd
    eqeq1d
    @43
    @48
    @56
    @2
    @43
    @48
    @5
    c1
    cmul
    co
    #
    @54
    caddc
    co
    @56
    @43
    @5
    c1
    @2
    @58
    @60
    @57
    adddid
    @43
    @61
    @5
    @54
    caddc
    @43
    @5
    @58
    mulid1d
    oveq1d
    eqtrd
    eqeq1d
    3bitr4rd
    @2
    @48
    eqcom
    @5
    @50
    eqcom
    3bitr4g
    @43
    @2
    @5
    @3
    @57
    @58
    @21
    @3
    cc
    wcel
    @8
    @42
    adantl
    @43
    @3
    @21
    @3
    crp
    wcel
    @8
    @38
    adantl
    rpne0d
    divmul3d
    @43
    @5
    @2
    @6
    @58
    @57
    @43
    @6
    @8
    @18
    @21
    @20
    adantr
    #
    rpcnd
    @43
    @6
    @62
    rpne0d
    divmul2d
    3bitr4d
    @5
    @4
    eqcom
    @2
    @7
    eqcom
    3bitr4g
    adantl
    f1ocnv2d
    trud
end
