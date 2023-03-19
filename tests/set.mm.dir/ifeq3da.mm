include "wa.mm"
include "wceq.mm"
include "cif.mm"
include "iftrue.mm"
include "syl.mm"
include "adantl.mm"
include "adantr.mm"
include "eqtr2d.mm"
include "wn.mm"
include "iffalse.mm"
include "ifeqda.mm"

theorem ifeq3da
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  assume ifeq3da.1: |- ( if ( ps , E , F ) = E -> C = G )
  assume ifeq3da.2: |- ( if ( ps , E , F ) = F -> C = H )
  assume ifeq3da.3: |- ( ph -> G = A )
  assume ifeq3da.4: |- ( ph -> H = B )


  assert |- ( ph -> if ( ps , A , B ) = C )

  proof
    wph
    wps
    cA
    cB
    cC
    wph
    wps
    wa
    cC
    cG
    cA
    wps
    cC
    cG
    wceq
    #
    wph
    wps
    wps
    cE
    cF
    cif
    #
    cE
    wceq
    @0
    wps
    cE
    cF
    iftrue
    ifeq3da.1
    syl
    adantl
    wph
    cG
    cA
    wceq
    wps
    ifeq3da.3
    adantr
    eqtr2d
    wph
    wps
    wn
    #
    wa
    cC
    cH
    cB
    @2
    cC
    cH
    wceq
    #
    wph
    @2
    @1
    cF
    wceq
    @3
    wps
    cE
    cF
    iffalse
    ifeq3da.2
    syl
    adantl
    wph
    cH
    cB
    wceq
    @2
    ifeq3da.4
    adantr
    eqtr2d
    ifeqda
end
