include "cun.mm"
include "cfv.mm"
include "cxad.mm"
include "co.mm"
include "caddc.mm"
include "meadjun.mm"
include "rexaddd.mm"
include "eqtrd.mm"

theorem meadjunre
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume meadjunre.m: |- ( ph -> M e. Meas )
  assume meadjunre.x: |- S = dom M
  assume meadjunre.a: |- ( ph -> A e. S )
  assume meadjunre.b: |- ( ph -> B e. S )
  assume meadjunre.d: |- ( ph -> ( A i^i B ) = (/) )
  assume meadjunre.r: |- ( ph -> ( M ` A ) e. RR )
  assume meadjunre.f: |- ( ph -> ( M ` B ) e. RR )


  assert |- ( ph -> ( M ` ( A u. B ) ) = ( ( M ` A ) + ( M ` B ) ) )

  proof
    wph
    cA
    cB
    cun
    cM
    cfv
    cA
    cM
    cfv
    #
    cB
    cM
    cfv
    #
    cxad
    co
    @0
    @1
    caddc
    co
    wph
    cA
    cB
    cS
    cM
    meadjunre.m
    meadjunre.x
    meadjunre.a
    meadjunre.b
    meadjunre.d
    meadjun
    wph
    @0
    @1
    meadjunre.r
    meadjunre.f
    rexaddd
    eqtrd
end
