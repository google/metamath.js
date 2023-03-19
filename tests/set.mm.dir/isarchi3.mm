include "cogrp.mm"
include "wcel.mm"
include "carchi.mm"
include "cv.mm"
include "wbr.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "cn.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "ctos.mm"
include "cmnd.mm"
include "wb.mm"
include "comnd.mm"
include "cgrp.mm"
include "isogrp.mm"
include "simprbi.mm"
include "omndtos.mm"
include "syl.mm"
include "wa.mm"
include "grpmnd.mm"
include "adantr.mm"
include "sylbi.mm"
include "eqid.mm"
include "isarchi2.mm"
include "syl2anc.mm"
include "c1.mm"
include "caddc.mm"
include "simpr.mm"
include "peano2nnd.mm"
include "cplusg.mm"
include "simp-4l.mm"
include "ogrpgrp.mm"
include "grpidcl.mm"
include "3syl.mm"
include "simp-4r.mm"
include "cz.mm"
include "ad4antr.mm"
include "nnzd.mm"
include "mulgcl.mm"
include "syl3anc.mm"
include "simpllr.mm"
include "ogrpaddlt.mm"
include "syl131anc.mm"
include "wceq.mm"
include "grplid.mm"
include "cc.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "addcom.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "csgrp.mm"
include "grpsgrp.mm"
include "1nn.mm"
include "a1i.mm"
include "mulgnndir.mm"
include "syl13anc.mm"
include "mulg1.mm"
include "3eqtrrd.mm"
include "3brtr3d.mm"
include "cpo.mm"
include "tospos.mm"
include "peano2zd.mm"
include "plelttr.mm"
include "impl.mm"
include "mpdan.mm"
include "oveq1.mm"
include "breq2d.mm"
include "rspcev.mm"
include "r19.29an.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "pltle.mm"
include "reximdva.mm"
include "imp.mm"
include "impbida.mm"
include "pm5.74da.mm"
include "ralbidva.mm"
include "bitrd.mm"

theorem isarchi3
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.lt: class .<
  let c.x: class .x.
  let vn: setvar n
  let cW: class W
  let c.0: class .0.
  let vm: setvar m
  assume isarchi3.b: |- B = ( Base ` W )
  assume isarchi3.0: |- .0. = ( 0g ` W )
  assume isarchi3.i: |- .< = ( lt ` W )
  assume isarchi3.x: |- .x. = ( .g ` W )

  disjoint n x
  disjoint n y
  disjoint x y
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint W n
  disjoint W x
  disjoint W y
  disjoint .< n
  disjoint .x. n
  disjoint .0. n
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint .< m
  disjoint .x. m
  assert |- ( W e. oGrp -> ( W e. Archi <-> A. x e. B A. y e. B ( .0. .< x -> E. n e. NN y .< ( n .x. x ) ) ) )

  proof
    cW
    cogrp
    wcel
    #
    cW
    carchi
    wcel
    #
    c.0
    vx
    cv
    #
    c.lt
    wbr
    #
    vy
    cv
    #
    vn
    cv
    #
    @2
    c.x
    co
    #
    cW
    cple
    cfv
    #
    wbr
    #
    vn
    cn
    wrex
    #
    wi
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @3
    @4
    @6
    c.lt
    wbr
    #
    vn
    cn
    wrex
    #
    wi
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    @0
    cW
    ctos
    wcel
    #
    cW
    cmnd
    wcel
    #
    @1
    @12
    wb
    @0
    cW
    comnd
    wcel
    #
    @17
    @0
    cW
    cgrp
    wcel
    #
    @19
    cW
    isogrp
    #
    simprbi
    cW
    omndtos
    syl
    #
    @0
    @20
    @19
    wa
    @18
    @21
    @20
    @18
    @19
    cW
    grpmnd
    adantr
    sylbi
    vx
    vy
    cB
    c.lt
    c.x
    vn
    @7
    cW
    c.0
    isarchi3.b
    isarchi3.0
    isarchi3.x
    @7
    eqid
    #
    isarchi3.i
    isarchi2
    syl2anc
    @0
    @11
    @16
    vx
    cB
    @0
    @2
    cB
    wcel
    #
    wa
    #
    @10
    @15
    vy
    cB
    @25
    @4
    cB
    wcel
    #
    wa
    #
    @3
    @9
    @14
    @27
    @3
    wa
    #
    @9
    @14
    @28
    @9
    wa
    @4
    vm
    cv
    #
    @2
    c.x
    co
    #
    c.lt
    wbr
    #
    vm
    cn
    wrex
    #
    @14
    @28
    @8
    @32
    vn
    cn
    @28
    @5
    cn
    wcel
    #
    wa
    #
    @8
    wa
    #
    @5
    c1
    caddc
    co
    #
    cn
    wcel
    @4
    @36
    @2
    c.x
    co
    #
    c.lt
    wbr
    #
    @32
    @35
    @5
    @34
    @33
    @8
    @28
    @33
    simpr
    #
    adantr
    #
    peano2nnd
    @35
    @6
    @37
    c.lt
    wbr
    #
    @38
    @35
    c.0
    @6
    cW
    cplusg
    cfv
    #
    co
    #
    @2
    @6
    @42
    co
    #
    @6
    @37
    c.lt
    @35
    @0
    c.0
    cB
    wcel
    #
    @24
    @6
    cB
    wcel
    #
    @3
    @43
    @44
    c.lt
    wbr
    @34
    @0
    @8
    @0
    @24
    @26
    @3
    @33
    simp-4l
    #
    adantr
    #
    @35
    @0
    @20
    @45
    @48
    cW
    ogrpgrp
    #
    cB
    cW
    c.0
    isarchi3.b
    isarchi3.0
    grpidcl
    3syl
    @34
    @24
    @8
    @0
    @24
    @26
    @3
    @33
    simp-4r
    #
    adantr
    #
    @34
    @46
    @8
    @34
    @20
    @5
    cz
    wcel
    @24
    @46
    @0
    @20
    @24
    @26
    @3
    @33
    @49
    ad4antr
    #
    @34
    @5
    @39
    nnzd
    #
    @50
    cB
    c.x
    cW
    @5
    @2
    isarchi3.b
    isarchi3.x
    mulgcl
    syl3anc
    #
    adantr
    #
    @27
    @3
    @33
    @8
    simpllr
    cB
    @42
    c.lt
    cW
    c.0
    @2
    @6
    isarchi3.b
    isarchi3.i
    @42
    eqid
    #
    ogrpaddlt
    syl131anc
    @35
    @20
    @46
    @43
    @6
    wceq
    @35
    @0
    @20
    @48
    @49
    syl
    @55
    cB
    @42
    cW
    @6
    c.0
    isarchi3.b
    @56
    isarchi3.0
    grplid
    syl2anc
    @35
    @37
    c1
    @5
    caddc
    co
    #
    @2
    c.x
    co
    #
    c1
    @2
    c.x
    co
    #
    @6
    @42
    co
    #
    @44
    @35
    @33
    @37
    @58
    wceq
    @40
    @33
    @36
    @57
    @2
    c.x
    @33
    @5
    cc
    wcel
    c1
    cc
    wcel
    @36
    @57
    wceq
    @5
    nncn
    ax-1cn
    @5
    c1
    addcom
    sylancl
    oveq1d
    syl
    @35
    cW
    csgrp
    wcel
    #
    c1
    cn
    wcel
    #
    @33
    @24
    @58
    @60
    wceq
    @35
    @0
    @20
    @61
    @48
    @49
    cW
    grpsgrp
    3syl
    @62
    @35
    1nn
    a1i
    @40
    @51
    cB
    @42
    c.x
    cW
    c1
    @5
    @2
    isarchi3.b
    isarchi3.x
    @56
    mulgnndir
    syl13anc
    @35
    @59
    @2
    @6
    @42
    @35
    @24
    @59
    @2
    wceq
    @51
    cB
    c.x
    cW
    @2
    isarchi3.b
    isarchi3.x
    mulg1
    syl
    oveq1d
    3eqtrrd
    3brtr3d
    @34
    @8
    @41
    @38
    @34
    cW
    cpo
    wcel
    #
    @26
    @46
    @37
    cB
    wcel
    #
    @8
    @41
    wa
    @38
    wi
    @34
    @0
    @17
    @63
    @47
    @22
    cW
    tospos
    3syl
    @25
    @26
    @3
    @33
    simpllr
    #
    @54
    @34
    @20
    @36
    cz
    wcel
    @24
    @64
    @52
    @34
    @5
    @53
    peano2zd
    @50
    cB
    c.x
    cW
    @36
    @2
    isarchi3.b
    isarchi3.x
    mulgcl
    syl3anc
    cB
    c.lt
    cW
    @7
    @4
    @6
    @37
    isarchi3.b
    @23
    isarchi3.i
    plelttr
    syl13anc
    impl
    mpdan
    @31
    @38
    vm
    @36
    cn
    @29
    @36
    wceq
    @30
    @37
    @4
    c.lt
    @29
    @36
    @2
    c.x
    oveq1
    breq2d
    rspcev
    syl2anc
    r19.29an
    @31
    @13
    vm
    vn
    cn
    @29
    @5
    wceq
    @30
    @6
    @4
    c.lt
    @29
    @5
    @2
    c.x
    oveq1
    breq2d
    cbvrexv
    sylib
    @28
    @14
    @9
    @28
    @13
    @8
    vn
    cn
    @34
    @0
    @26
    @46
    @13
    @8
    wi
    @47
    @65
    @54
    cogrp
    cB
    cB
    c.lt
    cW
    @7
    @4
    @6
    @23
    isarchi3.i
    pltle
    syl3anc
    reximdva
    imp
    impbida
    pm5.74da
    ralbidva
    ralbidva
    bitrd
end
