include "cseq.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "fveq2i.mm"
include "cuz.mm"
include "wcel.mm"
include "wceq.mm"
include "eleqtri.mm"
include "seqp1.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "syl5eqr.mm"
include "oveq12d.mm"
include "syl5eq.mm"

theorem seqp1i
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume seqp1i.1: |- Z = ( ZZ>= ` M )
  assume seqp1i.2: |- N e. Z
  assume seqp1i.3: |- K = ( N + 1 )
  assume seqp1i.4: |- ( ph -> ( seq M ( .+ , F ) ` N ) = A )
  assume seqp1i.5: |- ( ph -> ( F ` K ) = B )


  assert |- ( ph -> ( seq M ( .+ , F ) ` K ) = ( A .+ B ) )

  proof
    wph
    cK
    c.pl
    cF
    cM
    cseq
    #
    cfv
    #
    cN
    @0
    cfv
    #
    cN
    c1
    caddc
    co
    #
    cF
    cfv
    #
    c.pl
    co
    #
    cA
    cB
    c.pl
    co
    @1
    @3
    @0
    cfv
    #
    @5
    cK
    @3
    @0
    seqp1i.3
    fveq2i
    cN
    cM
    cuz
    cfv
    #
    wcel
    @6
    @5
    wceq
    cN
    cZ
    @7
    seqp1i.2
    seqp1i.1
    eleqtri
    c.pl
    cF
    cM
    cN
    seqp1
    ax-mp
    eqtri
    wph
    @2
    cA
    @4
    cB
    c.pl
    seqp1i.4
    wph
    @4
    cK
    cF
    cfv
    cB
    cK
    @3
    cF
    seqp1i.3
    fveq2i
    seqp1i.5
    syl5eqr
    oveq12d
    syl5eq
end
