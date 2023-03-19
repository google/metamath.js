include "cfv.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
include "cico.mm"
include "cvol.mm"
include "cprod.mm"
include "cif.mm"
include "cpnf.mm"
include "hoidmvval.mm"
include "wcel.mm"
include "0e0icopnf.mm"
include "a1i.mm"
include "cxr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cr.mm"
include "ffvelrnda.mm"
include "volico.mm"
include "syl2anc.mm"
include "resubcld.mm"
include "0red.mm"
include "ifcld.mm"
include "eqeltrd.mm"
include "fprodrecl.mm"
include "rexrd.mm"
include "nfv.mm"
include "cdm.mm"
include "cle.mm"
include "icombl.mm"
include "volge0.mm"
include "syl.mm"
include "fprodge0.mm"
include "ltpnfd.mm"
include "elicod.mm"

theorem hoidmvcl
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cL: class L
  let cX: class X
  let va: setvar a
  let vb: setvar b
  assume hoidmvcl.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume hoidmvcl.x: |- ( ph -> X e. Fin )
  assume hoidmvcl.a: |- ( ph -> A : X --> RR )
  assume hoidmvcl.b: |- ( ph -> B : X --> RR )

  disjoint A a
  disjoint A b
  disjoint A k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint B a
  disjoint B b
  disjoint B k
  disjoint X a
  disjoint X b
  disjoint X k
  disjoint X x
  disjoint a x
  disjoint b x
  disjoint k x
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( A ( L ` X ) B ) e. ( 0 [,) +oo ) )

  proof
    wph
    cA
    cB
    cX
    cL
    cfv
    co
    cX
    c0
    wceq
    #
    cc0
    cX
    vk
    cv
    #
    cA
    cfv
    #
    @1
    cB
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cif
    cc0
    cpnf
    cico
    co
    #
    wph
    vx
    cA
    cB
    vk
    cL
    cX
    va
    vb
    hoidmvcl.l
    hoidmvcl.a
    hoidmvcl.b
    hoidmvcl.x
    hoidmvval
    wph
    @0
    cc0
    @6
    @7
    cc0
    @7
    wcel
    wph
    0e0icopnf
    a1i
    wph
    cc0
    cpnf
    @6
    cc0
    cxr
    wcel
    wph
    0xr
    a1i
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    wph
    @6
    wph
    cX
    @5
    vk
    hoidmvcl.x
    wph
    @1
    cX
    wcel
    wa
    #
    @5
    @2
    @3
    clt
    wbr
    #
    @3
    @2
    cmin
    co
    #
    cc0
    cif
    #
    cr
    @8
    @2
    cr
    wcel
    #
    @3
    cr
    wcel
    @5
    @11
    wceq
    wph
    cX
    cr
    @1
    cA
    hoidmvcl.a
    ffvelrnda
    #
    wph
    cX
    cr
    @1
    cB
    hoidmvcl.b
    ffvelrnda
    #
    @2
    @3
    volico
    syl2anc
    @8
    @9
    @10
    cc0
    cr
    @8
    @3
    @2
    @14
    @13
    resubcld
    @8
    0red
    ifcld
    eqeltrd
    #
    fprodrecl
    #
    rexrd
    wph
    cX
    @5
    vk
    wph
    vk
    nfv
    hoidmvcl.x
    @15
    @8
    @4
    cvol
    cdm
    wcel
    #
    cc0
    @5
    cle
    wbr
    @8
    @12
    @3
    cxr
    wcel
    @17
    @13
    @8
    @3
    @14
    rexrd
    @2
    @3
    icombl
    syl2anc
    @4
    volge0
    syl
    fprodge0
    wph
    @6
    @16
    ltpnfd
    elicod
    ifcld
    eqeltrd
end
