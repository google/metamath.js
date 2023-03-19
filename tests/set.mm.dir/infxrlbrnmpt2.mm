include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "wss.mm"
include "wcel.mm"
include "clt.mm"
include "cinf.mm"
include "cle.mm"
include "wbr.mm"
include "eqid.mm"
include "rnmptssd.mm"
include "elrnmpt1s.mm"
include "syl2anc.mm"
include "infxrlb.mm"

theorem infxrlbrnmpt2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume infxrlbrnmpt2.x: |- F/ x ph
  assume infxrlbrnmpt2.b: |- ( ( ph /\ x e. A ) -> B e. RR* )
  assume infxrlbrnmpt2.c: |- ( ph -> C e. A )
  assume infxrlbrnmpt2.d: |- ( ph -> D e. RR* )
  assume infxrlbrnmpt2.e: |- ( x = C -> B = D )

  disjoint A x
  disjoint C x
  disjoint D x
  assert |- ( ph -> inf ( ran ( x e. A |-> B ) , RR* , < ) <_ D )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cxr
    wss
    cD
    @1
    wcel
    #
    @1
    cxr
    clt
    cinf
    cD
    cle
    wbr
    wph
    vx
    cA
    cB
    cxr
    @0
    infxrlbrnmpt2.x
    @0
    eqid
    #
    infxrlbrnmpt2.b
    rnmptssd
    wph
    cC
    cA
    wcel
    cD
    cxr
    wcel
    @2
    infxrlbrnmpt2.c
    infxrlbrnmpt2.d
    vx
    cA
    cB
    cD
    cC
    @0
    cxr
    @3
    infxrlbrnmpt2.e
    elrnmpt1s
    syl2anc
    @1
    cD
    infxrlb
    syl2anc
end
