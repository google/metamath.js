include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "c1.mm"
include "cmul.mm"
include "cc.mm"
include "ccncf.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "mptex2.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "eldifad.mm"
include "wne.mm"
include "eldifsni.mm"
include "divrecd.mm"
include "mpteq2dva.mm"
include "ccom.mm"
include "csb.mm"
include "ralrimiva.mm"
include "eqidd.mm"
include "fmptcos.mm"
include "wceq.mm"
include "csbov2g.mm"
include "csbvarg.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "eqtr2d.mm"
include "ax-1cn.mm"
include "eqid.mm"
include "cdivcncf.mm"
include "mp1i.mm"
include "cncfco.mm"
include "eqeltrd.mm"
include "mulcncf.mm"

theorem divcncf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cX: class X
  let vy: setvar y
  assume divcncf.1: |- ( ph -> ( x e. X |-> A ) e. ( X -cn-> CC ) )
  assume divcncf.2: |- ( ph -> ( x e. X |-> B ) e. ( X -cn-> ( CC \ { 0 } ) ) )

  disjoint X x
  disjoint ph x
  disjoint B y
  disjoint x y
  assert |- ( ph -> ( x e. X |-> ( A / B ) ) e. ( X -cn-> CC ) )

  proof
    wph
    vx
    cX
    cA
    cB
    cdiv
    co
    #
    cmpt
    vx
    cX
    cA
    c1
    cB
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    cX
    cc
    ccncf
    co
    #
    wph
    vx
    cX
    @0
    @2
    wph
    vx
    cv
    cX
    wcel
    wa
    #
    cA
    cB
    wph
    vx
    cX
    cA
    cc
    wph
    vx
    cX
    cA
    cmpt
    #
    @3
    wcel
    cX
    cc
    @5
    wf
    divcncf.1
    cX
    cc
    @5
    cncff
    syl
    mptex2
    @4
    cB
    cc
    cc0
    csn
    #
    wph
    vx
    cX
    cB
    cc
    @6
    cdif
    #
    wph
    vx
    cX
    cB
    cmpt
    #
    cX
    @7
    ccncf
    co
    wcel
    cX
    @7
    @8
    wf
    divcncf.2
    cX
    @7
    @8
    cncff
    syl
    mptex2
    #
    eldifad
    #
    @4
    cB
    @7
    wcel
    #
    cB
    cc0
    wne
    @9
    cB
    cc
    cc0
    eldifsni
    syl
    divrecd
    mpteq2dva
    wph
    vx
    cA
    @1
    cX
    divcncf.1
    wph
    vx
    cX
    @1
    cmpt
    #
    vy
    @7
    c1
    vy
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    @8
    ccom
    #
    @3
    wph
    @16
    vx
    cX
    vy
    cB
    @14
    csb
    #
    cmpt
    @12
    wph
    vx
    vy
    cX
    @7
    cB
    @14
    @8
    @15
    wph
    @11
    vx
    cX
    @9
    ralrimiva
    wph
    @8
    eqidd
    wph
    @15
    eqidd
    fmptcos
    wph
    vx
    cX
    @17
    @1
    @4
    @17
    c1
    vy
    cB
    @13
    csb
    #
    cdiv
    co
    #
    @1
    @4
    cB
    cc
    wcel
    #
    @17
    @19
    wceq
    @10
    vy
    cB
    c1
    @13
    cdiv
    cc
    csbov2g
    syl
    @4
    @18
    cB
    c1
    cdiv
    @4
    @20
    @18
    cB
    wceq
    @10
    vy
    cB
    cc
    csbvarg
    syl
    oveq2d
    eqtrd
    mpteq2dva
    eqtr2d
    wph
    cX
    @7
    cc
    @8
    @15
    divcncf.2
    c1
    cc
    wcel
    @15
    @7
    cc
    ccncf
    co
    wcel
    wph
    ax-1cn
    vy
    c1
    @15
    @15
    eqid
    cdivcncf
    mp1i
    cncfco
    eqeltrd
    mulcncf
    eqeltrd
end
