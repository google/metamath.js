include "wcel.mm"
include "wa.mm"
include "co.mm"
include "crh.mm"
include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "adantr.mm"
include "oveqd.mm"
include "ovres.mm"
include "adantl.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "biimp3a.mm"

theorem rhmresel
  let wph: wff ph
  let cB: class B
  let cF: class F
  let cH: class H
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume rhmresel.h: |- ( ph -> H = ( RingHom |` ( B X. B ) ) )


  assert |- ( ( ph /\ ( X e. B /\ Y e. B ) /\ F e. ( X H Y ) ) -> F e. ( X RingHom Y ) )

  proof
    wph
    cX
    cB
    wcel
    cY
    cB
    wcel
    wa
    #
    cF
    cX
    cY
    cH
    co
    #
    wcel
    cF
    cX
    cY
    crh
    co
    #
    wcel
    wph
    @0
    wa
    #
    @1
    @2
    cF
    @3
    @1
    cX
    cY
    crh
    cB
    cB
    cxp
    cres
    #
    co
    #
    @2
    @3
    cH
    @4
    cX
    cY
    wph
    cH
    @4
    wceq
    @0
    rhmresel.h
    adantr
    oveqd
    @0
    @5
    @2
    wceq
    wph
    cX
    cY
    cB
    cB
    crh
    ovres
    adantl
    eqtrd
    eleq2d
    biimp3a
end
