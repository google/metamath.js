include "cv.mm"
include "co.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "cn0.mm"
include "wrex.mm"
include "wn.mm"
include "cc0.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "ctos.mm"
include "wcel.mm"
include "wb.mm"
include "cogrp.mm"
include "comnd.mm"
include "cgrp.mm"
include "isogrp.mm"
include "simprbi.mm"
include "omndtos.mm"
include "3syl.mm"
include "ogrpgrp.mm"
include "syl.mm"
include "grpidcl.mm"
include "tltnle.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "mulg0.mm"
include "mtbird.mm"
include "cn.mm"
include "wi.mm"
include "wral.mm"
include "jca.mm"
include "cmnd.mm"
include "carchi.mm"
include "omndmnd.mm"
include "isarchi2.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "breq2.mm"
include "oveq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "breq1.mm"
include "imbi2d.mm"
include "rspc2v.mm"
include "syl3c.mm"
include "nn0min.mm"
include "adantr.mm"
include "cz.mm"
include "simpr.mm"
include "nn0zd.mm"
include "mulgcl.mm"
include "anbi1d.mm"
include "rexbidva.mm"
include "mpbird.mm"

theorem archirng
  let wph: wff ph
  let cB: class B
  let c.lt: class .<
  let c.x: class .x.
  let vn: setvar n
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  assume archirng.b: |- B = ( Base ` W )
  assume archirng.0: |- .0. = ( 0g ` W )
  assume archirng.i: |- .< = ( lt ` W )
  assume archirng.l: |- .<_ = ( le ` W )
  assume archirng.x: |- .x. = ( .g ` W )
  assume archirng.1: |- ( ph -> W e. oGrp )
  assume archirng.2: |- ( ph -> W e. Archi )
  assume archirng.3: |- ( ph -> X e. B )
  assume archirng.4: |- ( ph -> Y e. B )
  assume archirng.5: |- ( ph -> .0. .< X )
  assume archirng.6: |- ( ph -> .0. .< Y )

  disjoint X n
  disjoint Y n
  disjoint n ph
  disjoint .0. n
  disjoint .<_ n
  disjoint .< n
  disjoint .x. n
  disjoint m x
  disjoint m y
  disjoint B m
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint W m
  disjoint W x
  disjoint W y
  disjoint m n
  disjoint X m
  disjoint n x
  disjoint n y
  disjoint X x
  disjoint X y
  disjoint Y m
  disjoint Y y
  disjoint m ph
  disjoint .0. m
  disjoint .0. x
  disjoint .0. y
  disjoint .<_ m
  disjoint .<_ x
  disjoint .<_ y
  disjoint .< m
  disjoint .< x
  disjoint .< y
  disjoint .x. m
  disjoint .x. x
  disjoint .x. y
  assert |- ( ph -> E. n e. NN0 ( ( n .x. X ) .< Y /\ Y .<_ ( ( n + 1 ) .x. X ) ) )

  proof
    wph
    vn
    cv
    #
    cX
    c.x
    co
    #
    cY
    c.lt
    wbr
    #
    cY
    @0
    c1
    caddc
    co
    #
    cX
    c.x
    co
    #
    c.le
    wbr
    #
    wa
    #
    vn
    cn0
    wrex
    cY
    @1
    c.le
    wbr
    #
    wn
    #
    @5
    wa
    #
    vn
    cn0
    wrex
    wph
    cY
    vm
    cv
    #
    cX
    c.x
    co
    #
    c.le
    wbr
    #
    cY
    cc0
    cX
    c.x
    co
    #
    c.le
    wbr
    #
    @7
    @5
    vn
    vm
    @10
    cc0
    wceq
    @11
    @13
    cY
    c.le
    @10
    cc0
    cX
    c.x
    oveq1
    breq2d
    @10
    @0
    wceq
    @11
    @1
    cY
    c.le
    @10
    @0
    cX
    c.x
    oveq1
    breq2d
    @10
    @3
    wceq
    @11
    @4
    cY
    c.le
    @10
    @3
    cX
    c.x
    oveq1
    breq2d
    wph
    @14
    cY
    c.0
    c.le
    wbr
    #
    wph
    c.0
    cY
    c.lt
    wbr
    #
    @15
    wn
    #
    archirng.6
    wph
    cW
    ctos
    wcel
    #
    c.0
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @16
    @17
    wb
    wph
    cW
    cogrp
    wcel
    #
    cW
    comnd
    wcel
    #
    @18
    archirng.1
    @21
    cW
    cgrp
    wcel
    #
    @22
    cW
    isogrp
    simprbi
    #
    cW
    omndtos
    3syl
    #
    wph
    @23
    @19
    wph
    @21
    @23
    archirng.1
    cW
    ogrpgrp
    syl
    #
    cB
    cW
    c.0
    archirng.b
    archirng.0
    grpidcl
    syl
    archirng.4
    cB
    c.lt
    cW
    c.le
    c.0
    cY
    archirng.b
    archirng.l
    archirng.i
    tltnle
    syl3anc
    mpbid
    wph
    @13
    c.0
    cY
    c.le
    wph
    cX
    cB
    wcel
    #
    @13
    c.0
    wceq
    archirng.3
    cB
    c.x
    cW
    cX
    c.0
    archirng.b
    archirng.0
    archirng.x
    mulg0
    syl
    breq2d
    mtbird
    wph
    @27
    @20
    wa
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
    @10
    @28
    c.x
    co
    #
    c.le
    wbr
    #
    vm
    cn
    wrex
    #
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    c.0
    cX
    c.lt
    wbr
    #
    @12
    vm
    cn
    wrex
    #
    wph
    @27
    @20
    archirng.3
    archirng.4
    jca
    wph
    @18
    cW
    cmnd
    wcel
    #
    cW
    carchi
    wcel
    #
    @35
    @25
    wph
    @21
    @22
    @38
    archirng.1
    @24
    cW
    omndmnd
    3syl
    archirng.2
    @18
    @38
    wa
    @39
    @35
    vx
    vy
    cB
    c.lt
    c.x
    vm
    c.le
    cW
    c.0
    archirng.b
    archirng.0
    archirng.x
    archirng.l
    archirng.i
    isarchi2
    biimpa
    syl21anc
    archirng.5
    @34
    @36
    @37
    wi
    @36
    @30
    @11
    c.le
    wbr
    #
    vm
    cn
    wrex
    #
    wi
    vx
    vy
    cX
    cY
    cB
    cB
    @28
    cX
    wceq
    #
    @29
    @36
    @33
    @41
    @28
    cX
    c.0
    c.lt
    breq2
    @42
    @32
    @40
    vm
    cn
    @42
    @31
    @11
    @30
    c.le
    @28
    cX
    @10
    c.x
    oveq2
    breq2d
    rexbidv
    imbi12d
    @30
    cY
    wceq
    #
    @41
    @37
    @36
    @43
    @40
    @12
    vm
    cn
    @30
    cY
    @11
    c.le
    breq1
    rexbidv
    imbi2d
    rspc2v
    syl3c
    nn0min
    wph
    @6
    @9
    vn
    cn0
    wph
    @0
    cn0
    wcel
    #
    wa
    #
    @2
    @8
    @5
    @45
    @18
    @1
    cB
    wcel
    #
    @20
    @2
    @8
    wb
    wph
    @18
    @44
    @25
    adantr
    @45
    @23
    @0
    cz
    wcel
    @27
    @46
    wph
    @23
    @44
    @26
    adantr
    @45
    @0
    wph
    @44
    simpr
    nn0zd
    wph
    @27
    @44
    archirng.3
    adantr
    cB
    c.x
    cW
    @0
    cX
    archirng.b
    archirng.x
    mulgcl
    syl3anc
    wph
    @20
    @44
    archirng.4
    adantr
    cB
    c.lt
    cW
    c.le
    @1
    cY
    archirng.b
    archirng.l
    archirng.i
    tltnle
    syl3anc
    anbi1d
    rexbidva
    mpbird
end
