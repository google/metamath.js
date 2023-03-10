include "ke.mm"
include "kc.mm"
include "ax-cb1.mm"
include "ax-refl.mm"
include "a1i.mm"
include "hb.mm"
include "ht.mm"
include "weq.mm"
include "ax-ceq.mm"
include "syl2anc.mm"
include "wc.mm"
include "ax-eqmp.mm"

theorem eqcomx
  let hal: type al
  let ta: term A
  let tb: term B
  let tr: term R
  assume eqcomx.1: |- A : al
  assume eqcomx.2: |- B : al
  assume eqcomx.3: |- R |= ( ( = A ) B )


  assert |- R |= ( ( = B ) A )

  proof
    ke
    ta
    kc
    #
    ta
    kc
    #
    ke
    tb
    kc
    #
    ta
    kc
    #
    tr
    @1
    tr
    @0
    tb
    kc
    #
    tr
    eqcomx.3
    ax-cb1
    #
    hal
    ta
    eqcomx.1
    ax-refl
    a1i
    #
    ke
    @1
    kc
    @3
    kc
    tr
    ke
    @0
    kc
    @2
    kc
    #
    @1
    @7
    tr
    ke
    ke
    kc
    ke
    kc
    #
    @4
    @8
    tr
    @5
    hal
    hal
    hb
    ht
    #
    ht
    ke
    hal
    weq
    #
    ax-refl
    a1i
    eqcomx.3
    hal
    @9
    ta
    tb
    ke
    ke
    @10
    @10
    eqcomx.1
    eqcomx.2
    ax-ceq
    syl2anc
    @6
    hal
    hb
    ta
    ta
    @0
    @2
    hal
    @9
    ke
    ta
    @10
    eqcomx.1
    wc
    hal
    @9
    ke
    tb
    @10
    eqcomx.2
    wc
    eqcomx.1
    eqcomx.1
    ax-ceq
    syl2anc
    ax-eqmp
end
