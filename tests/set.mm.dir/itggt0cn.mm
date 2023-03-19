include "cc0.mm"
include "cr.mm"
include "cv.mm"
include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cfv.mm"
include "citg.mm"
include "clt.mm"
include "cpnf.mm"
include "cico.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "rpred.mm"
include "rpge0d.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "wn.mm"
include "0e0icopnf.mm"
include "a1i.mm"
include "ifclda.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "wral.mm"
include "rpgt0d.mm"
include "crp.mm"
include "wceq.mm"
include "elioore.mm"
include "adantl.mm"
include "iftrue.mm"
include "eqeltrd.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "ralrimiva.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfbr.mm"
include "nfv.mm"
include "weq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "cbvral.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "cres.mm"
include "cc.mm"
include "ccncf.mm"
include "wss.mm"
include "ioossre.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "mpteq2ia.mm"
include "eqtri.mm"
include "syl5eqel.mm"
include "itg2gt0cn.mm"
include "itgposval.mm"

theorem itggt0cn
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume itggt0cn.1: |- ( ph -> X < Y )
  assume itggt0cn.2: |- ( ph -> ( x e. ( X (,) Y ) |-> B ) e. L^1 )
  assume itggt0cn.3: |- ( ( ph /\ x e. ( X (,) Y ) ) -> B e. RR+ )
  assume itggt0cn.cn: |- ( ph -> ( x e. ( X (,) Y ) |-> B ) e. ( ( X (,) Y ) -cn-> CC ) )

  disjoint X x
  disjoint Y x
  disjoint ph x
  disjoint x y
  disjoint X y
  disjoint Y y
  disjoint B y
  disjoint ph y
  assert |- ( ph -> 0 < S. ( X (,) Y ) B _d x )

  proof
    wph
    cc0
    vx
    cr
    vx
    cv
    #
    cX
    cY
    cioo
    co
    #
    wcel
    #
    cB
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    vx
    @1
    cB
    citg
    clt
    wph
    vy
    @4
    cX
    cY
    itggt0cn.1
    wph
    vx
    cr
    @3
    cc0
    cpnf
    cico
    co
    #
    @4
    wph
    @3
    @5
    wcel
    @0
    cr
    wcel
    #
    wph
    @2
    cB
    cc0
    @5
    wph
    @2
    wa
    #
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    cB
    @5
    wcel
    @7
    cB
    itggt0cn.3
    rpred
    #
    @7
    cB
    itggt0cn.3
    rpge0d
    #
    cB
    elrege0
    sylanbrc
    cc0
    @5
    wcel
    wph
    @2
    wn
    wa
    0e0icopnf
    a1i
    ifclda
    adantr
    @4
    eqid
    #
    fmptd
    wph
    cc0
    vy
    cv
    #
    @4
    cfv
    #
    clt
    wbr
    #
    vy
    @1
    wph
    cc0
    @0
    @4
    cfv
    #
    clt
    wbr
    #
    vx
    @1
    wral
    @13
    vy
    @1
    wral
    wph
    @15
    vx
    @1
    @7
    cc0
    cB
    @14
    clt
    @7
    cB
    itggt0cn.3
    rpgt0d
    @7
    @14
    @3
    cB
    @7
    @6
    @3
    crp
    wcel
    @14
    @3
    wceq
    @2
    @6
    wph
    @0
    cX
    cY
    elioore
    adantl
    @7
    @3
    cB
    crp
    @2
    @3
    cB
    wceq
    wph
    @2
    cB
    cc0
    iftrue
    #
    adantl
    #
    itggt0cn.3
    eqeltrd
    vx
    cr
    @3
    crp
    @4
    @10
    fvmpt2
    syl2anc
    @17
    eqtrd
    breqtrrd
    ralrimiva
    @13
    @15
    vy
    vx
    @1
    vx
    cc0
    @12
    clt
    vx
    cc0
    nfcv
    vx
    clt
    nfcv
    vx
    cr
    @3
    @11
    nffvmpt1
    nfbr
    @15
    vy
    nfv
    vy
    vx
    weq
    @12
    @14
    cc0
    clt
    @11
    @0
    @4
    fveq2
    breq2d
    cbvral
    sylibr
    r19.21bi
    wph
    @4
    @1
    cres
    #
    vx
    @1
    cB
    cmpt
    #
    @1
    cc
    ccncf
    co
    @18
    vx
    @1
    @3
    cmpt
    #
    @19
    @1
    cr
    wss
    @18
    @20
    wceq
    cX
    cY
    ioossre
    vx
    cr
    @1
    @3
    resmpt
    ax-mp
    vx
    @1
    @3
    cB
    @16
    mpteq2ia
    eqtri
    itggt0cn.cn
    syl5eqel
    itg2gt0cn
    wph
    vx
    @1
    cB
    @8
    itggt0cn.2
    @9
    itgposval
    breqtrrd
end
