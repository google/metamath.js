include "cn0.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cmnd.mm"
include "co.mm"
include "csrg.mm"
include "srgmnd.mm"
include "syl.mm"
include "adantr.mm"
include "simpr1.mm"
include "srgbinomlem1.mm"
include "3adantr1.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"

theorem srgbinomlem2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cE: class E
  let c.ex: class .^
  let cG: class G
  let cN: class N
  assume srgbinom.s: |- S = ( Base ` R )
  assume srgbinom.m: |- .X. = ( .r ` R )
  assume srgbinom.t: |- .x. = ( .g ` R )
  assume srgbinom.a: |- .+ = ( +g ` R )
  assume srgbinom.g: |- G = ( mulGrp ` R )
  assume srgbinom.e: |- .^ = ( .g ` G )
  assume srgbinomlem.r: |- ( ph -> R e. SRing )
  assume srgbinomlem.a: |- ( ph -> A e. S )
  assume srgbinomlem.b: |- ( ph -> B e. S )
  assume srgbinomlem.c: |- ( ph -> ( A .X. B ) = ( B .X. A ) )
  assume srgbinomlem.n: |- ( ph -> N e. NN0 )


  assert |- ( ( ph /\ ( C e. NN0 /\ D e. NN0 /\ E e. NN0 ) ) -> ( C .x. ( ( D .^ A ) .X. ( E .^ B ) ) ) e. S )

  proof
    wph
    cC
    cn0
    wcel
    #
    cD
    cn0
    wcel
    #
    cE
    cn0
    wcel
    #
    w3a
    #
    wa
    cR
    cmnd
    wcel
    #
    @0
    cD
    cA
    c.ex
    co
    cE
    cB
    c.ex
    co
    c.xp
    co
    #
    cS
    wcel
    #
    cC
    @5
    c.x
    co
    cS
    wcel
    wph
    @4
    @3
    wph
    cR
    csrg
    wcel
    @4
    srgbinomlem.r
    cR
    srgmnd
    syl
    adantr
    wph
    @0
    @1
    @2
    simpr1
    wph
    @1
    @2
    @6
    @0
    wph
    cA
    cB
    cD
    c.pl
    cR
    cS
    c.x
    c.xp
    cE
    c.ex
    cG
    cN
    srgbinom.s
    srgbinom.m
    srgbinom.t
    srgbinom.a
    srgbinom.g
    srgbinom.e
    srgbinomlem.r
    srgbinomlem.a
    srgbinomlem.b
    srgbinomlem.c
    srgbinomlem.n
    srgbinomlem1
    3adantr1
    cS
    c.x
    cR
    cC
    @5
    srgbinom.s
    srgbinom.t
    mulgnn0cl
    syl3anc
end
