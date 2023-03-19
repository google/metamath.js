include "c0.mm"
include "cc.mm"
include "wcel.mm"
include "cmnf.mm"
include "wn.mm"
include "wa.mm"
include "cr.mm"
include "wf.mm"
include "cli.mm"
include "cdm.mm"
include "clsp.mm"
include "cfv.mm"
include "wbr.mm"
include "f0.mm"
include "cuz.mm"
include "cz.mm"
include "wceq.mm"
include "uz0.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "feq12i.mm"
include "mpbir.mm"
include "a1i.mm"
include "wrel.mm"
include "climrel.mm"
include "0cnv.mm"
include "syl5eqbr.mm"
include "releldm.mm"
include "syl2anc.mm"
include "adantr.mm"
include "adantlr.mm"
include "simpr.mm"
include "fveq2i.mm"
include "limsup0.mm"
include "breq12i.mm"
include "biimpi.mm"
include "climuni.mm"
include "adantll.mm"
include "nelneq.mm"
include "ad2antrr.mm"
include "pm2.65da.mm"
include "3jca.mm"

theorem climlimsupcex
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume climlimsupcex.1: |- -. M e. ZZ
  assume climlimsupcex.2: |- Z = ( ZZ>= ` M )
  assume climlimsupcex.3: |- F = (/)


  assert |- ( ( (/) e. CC /\ -. -oo e. CC ) -> ( F : Z --> RR /\ F e. dom ~~> /\ -. F ~~> ( limsup ` F ) ) )

  proof
    c0
    cc
    wcel
    #
    cmnf
    cc
    wcel
    wn
    #
    wa
    #
    cZ
    cr
    cF
    wf
    #
    cF
    cli
    cdm
    wcel
    #
    cF
    cF
    clsp
    cfv
    #
    cli
    wbr
    #
    wn
    @3
    @2
    @3
    c0
    cr
    c0
    wf
    cr
    f0
    cZ
    c0
    cr
    cF
    c0
    climlimsupcex.3
    cZ
    cM
    cuz
    cfv
    #
    c0
    climlimsupcex.2
    cM
    cz
    wcel
    wn
    @7
    c0
    wceq
    climlimsupcex.1
    cM
    uz0
    ax-mp
    eqtri
    feq12i
    mpbir
    a1i
    @0
    @4
    @1
    @0
    cli
    wrel
    #
    cF
    c0
    cli
    wbr
    @4
    @8
    @0
    climrel
    a1i
    @0
    cF
    c0
    c0
    cli
    climlimsupcex.3
    0cnv
    syl5eqbr
    cF
    c0
    cli
    releldm
    syl2anc
    adantr
    @2
    @6
    c0
    c0
    cli
    wbr
    #
    @0
    @6
    @9
    @1
    @0
    @9
    @6
    0cnv
    adantr
    adantlr
    @2
    @6
    wa
    @9
    c0
    cmnf
    wceq
    #
    @6
    @9
    @10
    @2
    @6
    @9
    wa
    @9
    c0
    cmnf
    cli
    wbr
    #
    @10
    @6
    @9
    simpr
    @6
    @11
    @9
    @6
    @11
    cF
    c0
    @5
    cmnf
    cli
    climlimsupcex.3
    @5
    c0
    clsp
    cfv
    cmnf
    cF
    c0
    clsp
    climlimsupcex.3
    fveq2i
    limsup0
    eqtri
    breq12i
    biimpi
    adantr
    c0
    cmnf
    c0
    climuni
    syl2anc
    adantll
    @2
    @10
    wn
    @6
    @9
    c0
    cmnf
    cc
    nelneq
    ad2antrr
    pm2.65da
    pm2.65da
    3jca
end
