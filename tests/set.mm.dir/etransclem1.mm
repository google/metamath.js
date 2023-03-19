include "cc.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cif.mm"
include "cexp.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "sselda.mm"
include "elfzelzd.mm"
include "zcnd.mm"
include "adantr.mm"
include "subcld.mm"
include "cn0.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nnnn0d.mm"
include "ifcld.mm"
include "expcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "cfz.mm"
include "cvv.mm"
include "oveq2.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "oveq12d.mm"
include "mpteq2dv.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "a1i.mm"
include "adantl.mm"
include "wss.mm"
include "cnex.mm"
include "ssex.mm"
include "mptexg.mm"
include "3syl.mm"
include "fvmptd.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem etransclem1
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let vj: setvar j
  let cH: class H
  let cJ: class J
  let cM: class M
  let cX: class X
  let vn: setvar n
  let vk: setvar k
  assume etransclem1.x: |- ( ph -> X C_ CC )
  assume etransclem1.p: |- ( ph -> P e. NN )
  assume etransclem1.h: |- H = ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem1.j: |- ( ph -> J e. ( 0 ... M ) )

  disjoint J x
  disjoint M j
  disjoint P j
  disjoint X j
  disjoint X x
  disjoint j x
  disjoint ph x
  disjoint J n
  disjoint n x
  disjoint M n
  disjoint j n
  disjoint P n
  disjoint X n
  disjoint n ph
  disjoint k x
  assert |- ( ph -> ( H ` J ) : X --> CC )

  proof
    wph
    cX
    cc
    cJ
    cH
    cfv
    #
    wf
    cX
    cc
    vx
    cX
    vx
    cv
    #
    cJ
    cmin
    co
    #
    cJ
    cc0
    wceq
    #
    cP
    c1
    cmin
    co
    #
    cP
    cif
    #
    cexp
    co
    #
    cmpt
    #
    wf
    wph
    vx
    cX
    @6
    cc
    @7
    wph
    @1
    cX
    wcel
    #
    wa
    #
    @2
    @5
    @9
    @1
    cJ
    wph
    cX
    cc
    @1
    etransclem1.x
    sselda
    wph
    cJ
    cc
    wcel
    @8
    wph
    cJ
    wph
    cJ
    cc0
    cM
    etransclem1.j
    elfzelzd
    zcnd
    adantr
    subcld
    wph
    @5
    cn0
    wcel
    @8
    wph
    @3
    @4
    cP
    cn0
    wph
    cP
    cn
    wcel
    @4
    cn0
    wcel
    etransclem1.p
    cP
    nnm1nn0
    syl
    wph
    cP
    etransclem1.p
    nnnn0d
    ifcld
    adantr
    expcld
    @7
    eqid
    fmptd
    wph
    cX
    cc
    @0
    @7
    wph
    vn
    cJ
    vx
    cX
    @1
    vn
    cv
    #
    cmin
    co
    #
    @10
    cc0
    wceq
    #
    @4
    cP
    cif
    #
    cexp
    co
    #
    cmpt
    #
    @7
    cc0
    cM
    cfz
    co
    #
    cH
    cvv
    cH
    vn
    @16
    @15
    cmpt
    #
    wceq
    wph
    cH
    vj
    @16
    vx
    cX
    @1
    vj
    cv
    #
    cmin
    co
    #
    @18
    cc0
    wceq
    #
    @4
    cP
    cif
    #
    cexp
    co
    #
    cmpt
    #
    cmpt
    @17
    etransclem1.h
    vj
    vn
    @16
    @23
    @15
    @18
    @10
    wceq
    #
    vx
    cX
    @22
    @14
    @24
    @19
    @11
    @21
    @13
    cexp
    @18
    @10
    @1
    cmin
    oveq2
    @24
    @20
    @12
    @4
    cP
    @18
    @10
    cc0
    eqeq1
    ifbid
    oveq12d
    mpteq2dv
    cbvmptv
    eqtri
    a1i
    @10
    cJ
    wceq
    #
    @15
    @7
    wceq
    wph
    @25
    vx
    cX
    @14
    @6
    @25
    @11
    @2
    @13
    @5
    cexp
    @10
    cJ
    @1
    cmin
    oveq2
    @25
    @12
    @3
    @4
    cP
    @10
    cJ
    cc0
    eqeq1
    ifbid
    oveq12d
    mpteq2dv
    adantl
    etransclem1.j
    wph
    cX
    cc
    wss
    cX
    cvv
    wcel
    @7
    cvv
    wcel
    etransclem1.x
    cX
    cc
    cnex
    ssex
    vx
    cX
    @6
    cvv
    mptexg
    3syl
    fvmptd
    feq1d
    mpbird
end
