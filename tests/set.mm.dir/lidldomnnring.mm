include "cdomn.mm"
include "wcel.mm"
include "csn.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "crg.mm"
include "wnel.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "neanior.mm"
include "biimpi.mm"
include "3adant1.mm"
include "adantl.mm"
include "df-nel.mm"
include "wb.mm"
include "uzlidlring.mm"
include "3ad2antr1.mm"
include "notbid.mm"
include "syl5bb.mm"
include "mpbird.mm"

theorem lidldomnnring
  let cB: class B
  let cR: class R
  let cU: class U
  let cI: class I
  let cL: class L
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume lidlabl.l: |- L = ( LIdeal ` R )
  assume lidlabl.i: |- I = ( R |`s U )
  assume zlidlring.b: |- B = ( Base ` R )
  assume zlidlring.0: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Domn /\ ( U e. L /\ U =/= { .0. } /\ U =/= B ) ) -> I e/ Ring )

  proof
    cR
    cdomn
    wcel
    #
    cU
    cL
    wcel
    #
    cU
    c.0
    csn
    #
    wne
    #
    cU
    cB
    wne
    #
    w3a
    #
    wa
    #
    cI
    crg
    wnel
    #
    cU
    @2
    wceq
    cU
    cB
    wceq
    wo
    #
    wn
    #
    @5
    @9
    @0
    @3
    @4
    @9
    @1
    @3
    @4
    wa
    @9
    cU
    @2
    cU
    cB
    neanior
    biimpi
    3adant1
    adantl
    @7
    cI
    crg
    wcel
    #
    wn
    @6
    @9
    cI
    crg
    df-nel
    @6
    @10
    @8
    @0
    @3
    @1
    @10
    @8
    wb
    @4
    cB
    cR
    cU
    cI
    cL
    c.0
    lidlabl.l
    lidlabl.i
    zlidlring.b
    zlidlring.0
    uzlidlring
    3ad2antr1
    notbid
    syl5bb
    mpbird
end
