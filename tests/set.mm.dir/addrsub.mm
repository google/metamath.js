include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "addcomd.mm"
include "eqeq1d.mm"
include "addlsub.mm"
include "bitrd.mm"

theorem addrsub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume addlsub.a: |- ( ph -> A e. CC )
  assume addlsub.b: |- ( ph -> B e. CC )
  assume addlsub.c: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A + B ) = C <-> B = ( C - A ) ) )

  proof
    wph
    cA
    cB
    caddc
    co
    #
    cC
    wceq
    cB
    cA
    caddc
    co
    #
    cC
    wceq
    cB
    cC
    cA
    cmin
    co
    wceq
    wph
    @0
    @1
    cC
    wph
    cA
    cB
    addlsub.a
    addlsub.b
    addcomd
    eqeq1d
    wph
    cB
    cA
    cC
    addlsub.b
    addlsub.a
    addlsub.c
    addlsub
    bitrd
end
