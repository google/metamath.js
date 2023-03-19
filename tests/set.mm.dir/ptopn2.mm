include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "cuni.mm"
include "cif.mm"
include "csn.mm"
include "cfn.mm"
include "wcel.mm"
include "snfi.mm"
include "a1i.mm"
include "wa.mm"
include "adantr.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "wn.mm"
include "ctop.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "topopn.mm"
include "syl.mm"
include "ifclda.mm"
include "cdif.mm"
include "eldifn.mm"
include "velsn.mm"
include "sylnib.mm"
include "iffalsed.mm"
include "adantl.mm"
include "ptopn.mm"

theorem ptopn2
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cO: class O
  let cV: class V
  let cY: class Y
  assume ptopn2.a: |- ( ph -> A e. V )
  assume ptopn2.f: |- ( ph -> F : A --> Top )
  assume ptopn2.o: |- ( ph -> O e. ( F ` Y ) )

  disjoint k ph
  disjoint A k
  disjoint F k
  disjoint V k
  disjoint Y k
  assert |- ( ph -> X_ k e. A if ( k = Y , O , U. ( F ` k ) ) e. ( Xt_ ` F ) )

  proof
    wph
    cA
    vk
    cv
    #
    cY
    wceq
    #
    cO
    @0
    cF
    cfv
    #
    cuni
    #
    cif
    #
    vk
    cF
    cV
    cY
    csn
    #
    ptopn2.a
    ptopn2.f
    @5
    cfn
    wcel
    wph
    cY
    snfi
    a1i
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @1
    cO
    @3
    @2
    @7
    @1
    cO
    @2
    wcel
    #
    @7
    @8
    @1
    cO
    cY
    cF
    cfv
    #
    wcel
    #
    wph
    @10
    @6
    ptopn2.o
    adantr
    @1
    @2
    @9
    cO
    @0
    cY
    cF
    fveq2
    eleq2d
    syl5ibrcom
    imp
    @7
    @3
    @2
    wcel
    #
    @1
    wn
    @7
    @2
    ctop
    wcel
    @11
    wph
    cA
    ctop
    @0
    cF
    ptopn2.f
    ffvelrnda
    @2
    @3
    @3
    eqid
    topopn
    syl
    adantr
    ifclda
    @0
    cA
    @5
    cdif
    wcel
    #
    @4
    @3
    wceq
    wph
    @12
    @1
    cO
    @3
    @12
    @0
    @5
    wcel
    @1
    @0
    cA
    @5
    eldifn
    vk
    cY
    velsn
    sylnib
    iffalsed
    adantl
    ptopn
end
