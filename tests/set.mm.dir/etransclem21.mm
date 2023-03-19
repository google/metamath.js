include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cif.mm"
include "clt.mm"
include "wbr.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "cdvn.mm"
include "cc.mm"
include "etransclem17.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "ifeq2d.mm"
include "adantl.mm"
include "wa.mm"
include "0cnd.mm"
include "wn.mm"
include "wcel.mm"
include "cn0.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nnnn0d.mm"
include "ifcld.mm"
include "faccld.mm"
include "nncnd.mm"
include "adantr.mm"
include "cz.mm"
include "cle.mm"
include "nn0zd.mm"
include "zsubcld.mm"
include "cr.mm"
include "nn0red.mm"
include "simpr.mm"
include "nltled.mm"
include "subge0d.mm"
include "mpbird.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "nnne0d.mm"
include "divcld.mm"
include "dvdmsscn.mm"
include "sseldd.mm"
include "elfzelzd.mm"
include "zcnd.mm"
include "subcld.mm"
include "expcld.mm"
include "mulcld.mm"
include "ifclda.mm"
include "fvmptd.mm"

theorem etransclem21
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cS: class S
  let vj: setvar j
  let cH: class H
  let cJ: class J
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume etransclem21.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem21.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem21.p: |- ( ph -> P e. NN )
  assume etransclem21.h: |- H = ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem21.j: |- ( ph -> J e. ( 0 ... M ) )
  assume etransclem21.n: |- ( ph -> N e. NN0 )
  assume etransclem21.y: |- ( ph -> Y e. X )

  disjoint J j
  disjoint J x
  disjoint j x
  disjoint M j
  disjoint M x
  disjoint N x
  disjoint P j
  disjoint P x
  disjoint S x
  disjoint X j
  disjoint X x
  disjoint Y x
  disjoint j ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( ( S Dn ( H ` J ) ) ` N ) ` Y ) = if ( if ( J = 0 , ( P - 1 ) , P ) < N , 0 , ( ( ( ! ` if ( J = 0 , ( P - 1 ) , P ) ) / ( ! ` ( if ( J = 0 , ( P - 1 ) , P ) - N ) ) ) x. ( ( Y - J ) ^ ( if ( J = 0 , ( P - 1 ) , P ) - N ) ) ) ) )

  proof
    wph
    vx
    cY
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
    cN
    clt
    wbr
    #
    cc0
    @2
    cfa
    cfv
    #
    @2
    cN
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    vx
    cv
    #
    cJ
    cmin
    co
    #
    @5
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    @3
    cc0
    @7
    cY
    cJ
    cmin
    co
    #
    @5
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    cX
    cN
    cS
    cJ
    cH
    cfv
    cdvn
    co
    cfv
    cc
    wph
    vx
    cP
    cS
    vj
    cH
    cJ
    cM
    cN
    cX
    etransclem21.s
    etransclem21.x
    etransclem21.p
    etransclem21.h
    etransclem21.j
    etransclem21.n
    etransclem17
    @8
    cY
    wceq
    #
    @12
    @16
    wceq
    wph
    @17
    @3
    @11
    @15
    cc0
    @17
    @10
    @14
    @7
    cmul
    @17
    @9
    @13
    @5
    cexp
    @8
    cY
    cJ
    cmin
    oveq1
    oveq1d
    oveq2d
    ifeq2d
    adantl
    etransclem21.y
    wph
    @3
    cc0
    @15
    cc
    wph
    @3
    wa
    0cnd
    wph
    @3
    wn
    #
    wa
    #
    @7
    @14
    @19
    @4
    @6
    wph
    @4
    cc
    wcel
    @18
    wph
    @4
    wph
    @2
    wph
    @0
    @1
    cP
    cn0
    wph
    cP
    cn
    wcel
    @1
    cn0
    wcel
    etransclem21.p
    cP
    nnm1nn0
    syl
    wph
    cP
    etransclem21.p
    nnnn0d
    ifcld
    #
    faccld
    nncnd
    adantr
    @19
    @6
    @19
    @5
    @19
    @5
    cz
    wcel
    #
    cc0
    @5
    cle
    wbr
    #
    @5
    cn0
    wcel
    wph
    @21
    @18
    wph
    @2
    cN
    wph
    @2
    @20
    nn0zd
    wph
    cN
    etransclem21.n
    nn0zd
    zsubcld
    adantr
    @19
    @22
    cN
    @2
    cle
    wbr
    @19
    cN
    @2
    wph
    cN
    cr
    wcel
    @18
    wph
    cN
    etransclem21.n
    nn0red
    adantr
    #
    wph
    @2
    cr
    wcel
    @18
    wph
    @2
    @20
    nn0red
    adantr
    #
    wph
    @18
    simpr
    nltled
    @19
    @2
    cN
    @24
    @23
    subge0d
    mpbird
    @5
    elnn0z
    sylanbrc
    #
    faccld
    #
    nncnd
    @19
    @6
    @26
    nnne0d
    divcld
    @19
    @13
    @5
    wph
    @13
    cc
    wcel
    @18
    wph
    cY
    cJ
    wph
    cX
    cc
    cY
    wph
    cS
    cX
    etransclem21.s
    etransclem21.x
    dvdmsscn
    etransclem21.y
    sseldd
    wph
    cJ
    wph
    cJ
    cc0
    cM
    etransclem21.j
    elfzelzd
    zcnd
    subcld
    adantr
    @25
    expcld
    mulcld
    ifclda
    fvmptd
end
