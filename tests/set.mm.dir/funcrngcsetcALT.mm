include "cop.mm"
include "cfunc.mm"
include "co.mm"
include "wcel.mm"
include "wbr.mm"
include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cmpt.mm"
include "cid.mm"
include "cmap.mm"
include "cres.mm"
include "cmpt2.mm"
include "crngh.mm"
include "ccofu.mm"
include "ccom.mm"
include "fveq2.mm"
include "cbvmptv.mm"
include "syl6eq.mm"
include "coires1.mm"
include "crng.mm"
include "cin.mm"
include "cwun.mm"
include "rngcbas.mm"
include "eleq2d.mm"
include "elin.mm"
include "simplbi.mm"
include "syl6bi.mm"
include "ssrdv.mm"
include "resmptd.mm"
include "syl5req.mm"
include "eqtrd.mm"
include "w3a.mm"
include "wf.mm"
include "eqid.mm"
include "rnghmf.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "syl5ibr.mm"
include "resabs1d.mm"
include "mpt2eq3dva.mm"
include "wceq.mm"
include "a1i.mm"
include "fvresi.mm"
include "adantr.mm"
include "adantl.mm"
include "oveq12d.mm"
include "eqidd.mm"
include "simprr.mm"
include "fveq2d.mm"
include "simprl.mm"
include "reseq2d.mm"
include "wi.mm"
include "com12.mm"
include "impcom.mm"
include "a1d.mm"
include "imp32.mm"
include "ovex.mm"
include "resiexd.mm"
include "ovmpt2d.mm"
include "eqtr2d.mm"
include "oveq12.mm"
include "eqcomd.mm"
include "coeq12d.mm"
include "mpt2eq123dva.mm"
include "opeq12d.mm"
include "cestrc.mm"
include "rngcifuestrc.mm"
include "estrcbas.mm"
include "mpteq1d.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "cbvmpt2v.mm"
include "mpt2eq123dv.mm"
include "funcestrcsetc.mm"
include "cofuval2.mm"
include "eqtr4d.mm"
include "df-br.mm"
include "sylib.mm"
include "cofucl.mm"
include "eqeltrd.mm"
include "sylibr.mm"

theorem funcrngcsetcALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  let vv: setvar v
  let vk: setvar k
  assume funcrngcsetcALT.r: |- R = ( RngCat ` U )
  assume funcrngcsetcALT.s: |- S = ( SetCat ` U )
  assume funcrngcsetcALT.b: |- B = ( Base ` R )
  assume funcrngcsetcALT.u: |- ( ph -> U e. WUni )
  assume funcrngcsetcALT.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcrngcsetcALT.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( x RngHomo y ) ) ) )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint R x
  disjoint R y
  disjoint U x
  disjoint U y
  disjoint ph x
  disjoint ph y
  disjoint B f
  disjoint B g
  disjoint B u
  disjoint B w
  disjoint B z
  disjoint f g
  disjoint f u
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g u
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint R f
  disjoint R g
  disjoint S u
  disjoint U f
  disjoint U g
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U z
  disjoint f v
  disjoint g v
  disjoint u v
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint f ph
  disjoint g ph
  disjoint ph w
  disjoint ph u
  disjoint ph v
  disjoint ph z
  disjoint k x
  assert |- ( ph -> F ( R Func S ) G )

  proof
    wph
    cF
    cG
    cop
    #
    cR
    cS
    cfunc
    co
    #
    wcel
    cF
    cG
    @1
    wbr
    wph
    @0
    vu
    cU
    vu
    cv
    #
    cbs
    cfv
    #
    cmpt
    #
    vw
    vz
    cU
    cU
    cid
    vz
    cv
    #
    cbs
    cfv
    #
    vw
    cv
    #
    cbs
    cfv
    #
    cmap
    co
    #
    cres
    #
    cmpt2
    #
    cop
    #
    cid
    cB
    cres
    #
    vf
    vg
    cB
    cB
    cid
    vf
    cv
    #
    vg
    cv
    #
    crngh
    co
    #
    cres
    #
    cmpt2
    #
    cop
    #
    ccofu
    co
    #
    @1
    wph
    @0
    @4
    @13
    ccom
    #
    vx
    vy
    cR
    cbs
    cfv
    #
    @22
    vx
    cv
    #
    @13
    cfv
    #
    vy
    cv
    #
    @13
    cfv
    #
    @11
    co
    #
    @23
    @25
    @18
    co
    #
    ccom
    #
    cmpt2
    #
    cop
    @20
    wph
    cF
    @21
    cG
    @30
    wph
    cF
    vu
    cB
    @3
    cmpt
    #
    @21
    wph
    cF
    vx
    cB
    @23
    cbs
    cfv
    #
    cmpt
    @31
    funcrngcsetcALT.f
    vx
    vu
    cB
    @32
    @3
    @23
    @2
    cbs
    fveq2
    cbvmptv
    syl6eq
    wph
    @21
    @4
    cB
    cres
    @31
    @4
    cB
    coires1
    wph
    vu
    cU
    cB
    @3
    wph
    vx
    cB
    cU
    wph
    @23
    cB
    wcel
    #
    @23
    cU
    crng
    cin
    #
    wcel
    #
    @23
    cU
    wcel
    #
    wph
    cB
    @34
    @23
    wph
    cB
    cR
    cU
    cwun
    funcrngcsetcALT.r
    funcrngcsetcALT.b
    funcrngcsetcALT.u
    rngcbas
    #
    eleq2d
    @35
    @36
    @23
    crng
    wcel
    @23
    cU
    crng
    elin
    simplbi
    syl6bi
    #
    ssrdv
    resmptd
    syl5req
    eqtrd
    wph
    cG
    vx
    vy
    cB
    cB
    cid
    @25
    cbs
    cfv
    #
    @32
    cmap
    co
    #
    cres
    #
    cid
    @23
    @25
    crngh
    co
    #
    cres
    #
    ccom
    #
    cmpt2
    #
    @30
    wph
    cG
    vx
    vy
    cB
    cB
    @43
    cmpt2
    @45
    funcrngcsetcALT.g
    wph
    vx
    vy
    cB
    cB
    @43
    @44
    wph
    @33
    @25
    cB
    wcel
    #
    w3a
    #
    @44
    @41
    @42
    cres
    @43
    @41
    @42
    coires1
    @47
    cid
    @42
    @40
    @47
    vz
    @42
    @40
    @5
    @42
    wcel
    @5
    @40
    wcel
    #
    @47
    @32
    @39
    @5
    wf
    #
    @32
    @39
    @23
    @25
    @5
    @32
    eqid
    @39
    eqid
    rnghmf
    @39
    cvv
    wcel
    #
    @32
    cvv
    wcel
    #
    wa
    @48
    @49
    wb
    @47
    @50
    @51
    @25
    cbs
    fvex
    @23
    cbs
    fvex
    pm3.2i
    @39
    @32
    @5
    cvv
    cvv
    elmapg
    mp1i
    syl5ibr
    ssrdv
    resabs1d
    syl5req
    mpt2eq3dva
    eqtrd
    wph
    vx
    vy
    cB
    cB
    @44
    @22
    @22
    @29
    cB
    @22
    wceq
    #
    wph
    funcrngcsetcALT.b
    a1i
    @52
    wph
    @33
    wa
    funcrngcsetcALT.b
    a1i
    wph
    @33
    @46
    wa
    #
    wa
    #
    @41
    @27
    @43
    @28
    @54
    @27
    @23
    @25
    @11
    co
    @41
    @54
    @24
    @23
    @26
    @25
    @11
    @53
    @24
    @23
    wceq
    #
    wph
    @33
    @55
    @46
    cB
    @23
    fvresi
    adantr
    adantl
    @53
    @26
    @25
    wceq
    #
    wph
    @46
    @56
    @33
    cB
    @25
    fvresi
    adantl
    adantl
    oveq12d
    @54
    vw
    vz
    @23
    @25
    cU
    cU
    @10
    @41
    @11
    cvv
    @54
    @11
    eqidd
    @54
    @7
    @23
    wceq
    #
    @5
    @25
    wceq
    #
    wa
    wa
    #
    @9
    @40
    cid
    @59
    @6
    @39
    @8
    @32
    cmap
    @59
    @5
    @25
    cbs
    @54
    @57
    @58
    simprr
    fveq2d
    @59
    @7
    @23
    cbs
    @54
    @57
    @58
    simprl
    fveq2d
    oveq12d
    reseq2d
    @53
    wph
    @36
    @33
    wph
    @36
    wi
    @46
    wph
    @33
    @36
    @38
    com12
    adantr
    impcom
    wph
    @33
    @46
    @25
    cU
    wcel
    #
    wph
    @46
    @60
    wi
    @33
    wph
    @46
    @25
    @34
    wcel
    #
    @60
    wph
    cB
    @34
    @25
    @37
    eleq2d
    @61
    @60
    @25
    crng
    wcel
    @25
    cU
    crng
    elin
    simplbi
    syl6bi
    a1d
    imp32
    @54
    @40
    cvv
    @40
    cvv
    wcel
    @54
    @39
    @32
    cmap
    ovex
    a1i
    resiexd
    ovmpt2d
    eqtr2d
    @54
    @28
    @43
    @54
    vf
    vg
    @23
    @25
    cB
    cB
    @17
    @43
    @18
    cvv
    @54
    @18
    eqidd
    @14
    @23
    wceq
    @15
    @25
    wceq
    wa
    #
    @17
    @43
    wceq
    @54
    @62
    @16
    @42
    cid
    @14
    @23
    @15
    @25
    crngh
    oveq12
    reseq2d
    adantl
    wph
    @33
    @46
    simprl
    wph
    @33
    @46
    simprr
    @54
    @42
    cvv
    @42
    cvv
    wcel
    @54
    @23
    @25
    crngh
    ovex
    a1i
    resiexd
    ovmpt2d
    eqcomd
    coeq12d
    mpt2eq123dva
    eqtrd
    opeq12d
    wph
    vx
    vy
    @22
    cR
    cU
    cestrc
    cfv
    #
    cS
    @13
    @18
    @4
    @11
    @22
    eqid
    wph
    vf
    vg
    cB
    cR
    cU
    @63
    @13
    @18
    cwun
    funcrngcsetcALT.r
    @63
    eqid
    #
    funcrngcsetcALT.b
    funcrngcsetcALT.u
    wph
    @13
    eqidd
    wph
    @18
    eqidd
    rngcifuestrc
    #
    wph
    vu
    vv
    @63
    cbs
    cfv
    #
    cS
    cbs
    cfv
    #
    cS
    cU
    @63
    @4
    @11
    @64
    funcrngcsetcALT.s
    @66
    eqid
    @67
    eqid
    funcrngcsetcALT.u
    wph
    vu
    cU
    @66
    @3
    wph
    @63
    cU
    cwun
    @64
    funcrngcsetcALT.u
    estrcbas
    #
    mpteq1d
    wph
    @11
    vu
    vv
    cU
    cU
    cid
    vv
    cv
    #
    cbs
    cfv
    #
    @3
    cmap
    co
    #
    cres
    #
    cmpt2
    #
    vu
    vv
    @66
    @66
    @72
    cmpt2
    @11
    @73
    wceq
    wph
    vw
    vz
    vu
    vv
    cU
    cU
    @10
    @72
    cid
    @6
    @3
    cmap
    co
    #
    cres
    @7
    @2
    wceq
    #
    @9
    @74
    cid
    @75
    @8
    @3
    @6
    cmap
    @7
    @2
    cbs
    fveq2
    oveq2d
    reseq2d
    @5
    @69
    wceq
    #
    @74
    @71
    cid
    @76
    @6
    @70
    @3
    cmap
    @5
    @69
    cbs
    fveq2
    oveq1d
    reseq2d
    cbvmpt2v
    a1i
    wph
    vu
    vv
    cU
    cU
    @72
    @66
    @66
    @72
    @68
    @68
    wph
    @72
    eqidd
    mpt2eq123dv
    eqtrd
    funcestrcsetc
    #
    cofuval2
    eqtr4d
    wph
    cR
    @63
    cS
    @19
    @12
    wph
    @13
    @18
    cR
    @63
    cfunc
    co
    #
    wbr
    @19
    @78
    wcel
    @65
    @13
    @18
    @78
    df-br
    sylib
    wph
    @4
    @11
    @63
    cS
    cfunc
    co
    #
    wbr
    @12
    @79
    wcel
    @77
    @4
    @11
    @79
    df-br
    sylib
    cofucl
    eqeltrd
    cF
    cG
    @1
    df-br
    sylibr
end
