include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "csrg.mm"
include "co.mm"
include "adantr.mm"
include "cmnd.mm"
include "srgmgp.mm"
include "syl.mm"
include "simprl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "simprr.mm"
include "srgcl.mm"

theorem srgbinomlem1
  let wph: wff ph
  let cA: class A
  let cB: class B
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


  assert |- ( ( ph /\ ( D e. NN0 /\ E e. NN0 ) ) -> ( ( D .^ A ) .X. ( E .^ B ) ) e. S )

  proof
    wph
    cD
    cn0
    wcel
    #
    cE
    cn0
    wcel
    #
    wa
    #
    wa
    #
    cR
    csrg
    wcel
    #
    cD
    cA
    c.ex
    co
    #
    cS
    wcel
    #
    cE
    cB
    c.ex
    co
    #
    cS
    wcel
    #
    @5
    @7
    c.xp
    co
    cS
    wcel
    wph
    @4
    @2
    srgbinomlem.r
    adantr
    @3
    cG
    cmnd
    wcel
    #
    @0
    cA
    cS
    wcel
    #
    @6
    wph
    @9
    @2
    wph
    @4
    @9
    srgbinomlem.r
    cR
    cG
    srgbinom.g
    srgmgp
    syl
    adantr
    #
    wph
    @0
    @1
    simprl
    wph
    @10
    @2
    srgbinomlem.a
    adantr
    cS
    c.ex
    cG
    cD
    cA
    cS
    cR
    cG
    srgbinom.g
    srgbinom.s
    mgpbas
    #
    srgbinom.e
    mulgnn0cl
    syl3anc
    @3
    @9
    @1
    cB
    cS
    wcel
    #
    @8
    @11
    wph
    @0
    @1
    simprr
    wph
    @13
    @2
    srgbinomlem.b
    adantr
    cS
    c.ex
    cG
    cE
    cB
    @12
    srgbinom.e
    mulgnn0cl
    syl3anc
    cS
    cR
    c.xp
    @5
    @7
    srgbinom.s
    srgbinom.m
    srgcl
    syl3anc
end
