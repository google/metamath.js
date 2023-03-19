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
include "chom.mm"
include "cresf.mm"
include "cestrc.mm"
include "cresc.mm"
include "eqid.mm"
include "cwun.mm"
include "estrcbas.mm"
include "mpteq1d.mm"
include "wceq.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "funcestrcsetc.mm"
include "df-br.mm"
include "sylib.mm"
include "crg.mm"
include "cin.mm"
include "ringcbas.mm"
include "incom.mm"
include "syl6eq.mm"
include "ringchomfval.mm"
include "rhmsubcsetc.mm"
include "funcres.mm"
include "cvv.mm"
include "mptexg.mm"
include "syl.mm"
include "fvex.mm"
include "a1i.mm"
include "mpt2exga.mm"
include "rhmresfn.mm"
include "resfval2.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "resmptd.mm"
include "eqtr2d.mm"
include "eqtrd.mm"
include "crh.mm"
include "oveq1.mm"
include "reseq2d.mm"
include "oveq2.mm"
include "cbvmpt2v.mm"
include "wa.mm"
include "eqidd.mm"
include "fveq2.mm"
include "oveqan12rd.mm"
include "adantl.mm"
include "wi.mm"
include "syl5eqss.mm"
include "sseld.mm"
include "com12.mm"
include "adantr.mm"
include "impcom.mm"
include "adantld.mm"
include "imp.mm"
include "ovexd.mm"
include "resiexd.mm"
include "ovmpt2d.mm"
include "reseq1d.mm"
include "simprl.mm"
include "simprr.mm"
include "ringchom.mm"
include "wf.mm"
include "rhmf.mm"
include "wb.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "syl5ibr.mm"
include "ssrdv.mm"
include "resabs1d.mm"
include "3eqtrrd.mm"
include "mpt2eq123dva.mm"
include "opeq12d.mm"
include "ringcval.mm"
include "oveq1d.mm"
include "3eltr4d.mm"
include "sylibr.mm"

theorem funcringcsetc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vk: setvar k
  assume funcringcsetc.r: |- R = ( RingCat ` U )
  assume funcringcsetc.s: |- S = ( SetCat ` U )
  assume funcringcsetc.b: |- B = ( Base ` R )
  assume funcringcsetc.u: |- ( ph -> U e. WUni )
  assume funcringcsetc.f: |- ( ph -> F = ( x e. B |-> ( Base ` x ) ) )
  assume funcringcsetc.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( x RingHom y ) ) ) )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint R x
  disjoint S x
  disjoint U x
  disjoint U y
  disjoint ph x
  disjoint ph y
  disjoint B a
  disjoint B b
  disjoint B f
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint f x
  disjoint f y
  disjoint R a
  disjoint R b
  disjoint U a
  disjoint U b
  disjoint a ph
  disjoint b ph
  disjoint f ph
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
    vx
    cU
    vx
    cv
    #
    cbs
    cfv
    #
    cmpt
    #
    vx
    vy
    cU
    cU
    cid
    vy
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
    cop
    #
    cR
    chom
    cfv
    #
    cresf
    co
    #
    cU
    cestrc
    cfv
    #
    @11
    cresc
    co
    #
    cS
    cfunc
    co
    @0
    @1
    wph
    @13
    cS
    @10
    @11
    wph
    @4
    @9
    @13
    cS
    cfunc
    co
    #
    wbr
    @10
    @15
    wcel
    wph
    vx
    vy
    @13
    cbs
    cfv
    #
    cS
    cbs
    cfv
    #
    cS
    cU
    @13
    @4
    @9
    @13
    eqid
    #
    funcringcsetc.s
    @16
    eqid
    @17
    eqid
    funcringcsetc.u
    wph
    vx
    cU
    @16
    @3
    wph
    @13
    cU
    cwun
    @18
    funcringcsetc.u
    estrcbas
    #
    mpteq1d
    wph
    cU
    @16
    wceq
    #
    @20
    @9
    vx
    vy
    @16
    @16
    @8
    cmpt2
    wceq
    @19
    @19
    vx
    vy
    cU
    cU
    @16
    @16
    @8
    mpt2eq12
    syl2anc
    funcestrcsetc
    @4
    @9
    @15
    df-br
    sylib
    wph
    cR
    cbs
    cfv
    #
    @13
    cU
    @11
    cwun
    @18
    funcringcsetc.u
    wph
    @21
    cU
    crg
    cin
    #
    crg
    cU
    cin
    wph
    @21
    cR
    cU
    cwun
    funcringcsetc.r
    @21
    eqid
    #
    funcringcsetc.u
    ringcbas
    #
    cU
    crg
    incom
    syl6eq
    wph
    @21
    cR
    cU
    @11
    cwun
    funcringcsetc.r
    @23
    funcringcsetc.u
    @11
    eqid
    #
    ringchomfval
    #
    rhmsubcsetc
    funcres
    wph
    @12
    @4
    @21
    cres
    #
    va
    vb
    @21
    @21
    va
    cv
    #
    vb
    cv
    #
    @9
    co
    #
    @28
    @29
    @11
    co
    #
    cres
    #
    cmpt2
    #
    cop
    @0
    wph
    va
    vb
    @21
    @4
    @9
    @11
    cvv
    cvv
    cvv
    wph
    cU
    cwun
    wcel
    #
    @4
    cvv
    wcel
    funcringcsetc.u
    vx
    cU
    @3
    cwun
    mptexg
    syl
    @11
    cvv
    wcel
    wph
    cR
    chom
    fvex
    a1i
    wph
    @34
    @34
    @9
    cvv
    wcel
    funcringcsetc.u
    funcringcsetc.u
    vx
    vy
    cU
    cU
    @8
    cwun
    cwun
    mpt2exga
    syl2anc
    wph
    @21
    cU
    @11
    @24
    @26
    rhmresfn
    resfval2
    wph
    @27
    cF
    @33
    cG
    wph
    @27
    vx
    @21
    @3
    cmpt
    #
    cF
    wph
    vx
    cU
    @21
    @3
    wph
    @21
    @22
    cU
    @24
    cU
    crg
    inss1
    syl6eqss
    #
    resmptd
    wph
    cF
    vx
    cB
    @3
    cmpt
    @35
    funcringcsetc.f
    wph
    vx
    cB
    @21
    @3
    cB
    @21
    wceq
    #
    wph
    funcringcsetc.b
    a1i
    #
    mpteq1d
    eqtr2d
    eqtrd
    wph
    cG
    vx
    vy
    cB
    cB
    cid
    @2
    @5
    crh
    co
    #
    cres
    #
    cmpt2
    #
    va
    vb
    cB
    cB
    cid
    @28
    @29
    crh
    co
    #
    cres
    #
    cmpt2
    #
    @33
    funcringcsetc.g
    @41
    @44
    wceq
    wph
    vx
    vy
    va
    vb
    cB
    cB
    @40
    @43
    cid
    @28
    @5
    crh
    co
    #
    cres
    @2
    @28
    wceq
    #
    @39
    @45
    cid
    @2
    @28
    @5
    crh
    oveq1
    reseq2d
    @5
    @29
    wceq
    #
    @45
    @42
    cid
    @5
    @29
    @28
    crh
    oveq2
    reseq2d
    cbvmpt2v
    a1i
    wph
    va
    vb
    cB
    cB
    @43
    @21
    @21
    @32
    @38
    @37
    wph
    @28
    cB
    wcel
    #
    wa
    funcringcsetc.b
    a1i
    wph
    @48
    @29
    cB
    wcel
    #
    wa
    #
    wa
    #
    @32
    cid
    @29
    cbs
    cfv
    #
    @28
    cbs
    cfv
    #
    cmap
    co
    #
    cres
    #
    @31
    cres
    @55
    @42
    cres
    @43
    @51
    @30
    @55
    @31
    @51
    vx
    vy
    @28
    @29
    cU
    cU
    @8
    @55
    @9
    cvv
    @51
    @9
    eqidd
    @46
    @47
    wa
    #
    @8
    @55
    wceq
    @51
    @56
    @7
    @54
    cid
    @47
    @46
    @6
    @52
    @3
    @53
    cmap
    @5
    @29
    cbs
    fveq2
    @2
    @28
    cbs
    fveq2
    oveqan12rd
    reseq2d
    adantl
    @50
    wph
    @28
    cU
    wcel
    #
    @48
    wph
    @57
    wi
    @49
    wph
    @48
    @57
    wph
    cB
    cU
    @28
    wph
    cB
    @21
    cU
    funcringcsetc.b
    @36
    syl5eqss
    #
    sseld
    com12
    adantr
    impcom
    wph
    @50
    @29
    cU
    wcel
    #
    wph
    @49
    @59
    @48
    wph
    cB
    cU
    @29
    @58
    sseld
    adantld
    imp
    @51
    @54
    cvv
    @51
    @52
    @53
    cmap
    ovexd
    resiexd
    ovmpt2d
    reseq1d
    @51
    @31
    @42
    @55
    @51
    cB
    cR
    cU
    @11
    cwun
    @28
    @29
    funcringcsetc.r
    funcringcsetc.b
    wph
    @34
    @50
    funcringcsetc.u
    adantr
    @25
    wph
    @48
    @49
    simprl
    wph
    @48
    @49
    simprr
    ringchom
    reseq2d
    @51
    cid
    @42
    @54
    @51
    vf
    @42
    @54
    vf
    cv
    #
    @42
    wcel
    @60
    @54
    wcel
    #
    @51
    @53
    @52
    @60
    wf
    #
    @53
    @52
    @28
    @29
    @60
    @53
    eqid
    @52
    eqid
    rhmf
    @51
    @52
    cvv
    wcel
    #
    @53
    cvv
    wcel
    #
    wa
    #
    @61
    @62
    wb
    @65
    @51
    @63
    @64
    @29
    cbs
    fvex
    @28
    cbs
    fvex
    pm3.2i
    a1i
    @52
    @53
    @60
    cvv
    cvv
    elmapg
    syl
    syl5ibr
    ssrdv
    resabs1d
    3eqtrrd
    mpt2eq123dva
    3eqtrrd
    opeq12d
    eqtr2d
    wph
    cR
    @14
    cS
    cfunc
    wph
    @21
    cR
    cU
    @11
    cwun
    funcringcsetc.r
    funcringcsetc.u
    @24
    @26
    ringcval
    oveq1d
    3eltr4d
    cF
    cG
    @1
    df-br
    sylibr
end
