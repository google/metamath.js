include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cabl.mm"
include "csubg.mm"
include "cfv.mm"
include "ringabl.mm"
include "adantr.mm"
include "lidlsubg.mm"
include "subgabl.mm"
include "syl2anc.mm"

theorem lidlabl
  let cR: class R
  let cU: class U
  let cI: class I
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x
  assume lidlabl.l: |- L = ( LIdeal ` R )
  assume lidlabl.i: |- I = ( R |`s U )


  assert |- ( ( R e. Ring /\ U e. L ) -> I e. Abel )

  proof
    cR
    crg
    wcel
    #
    cU
    cL
    wcel
    #
    wa
    cR
    cabl
    wcel
    #
    cU
    cR
    csubg
    cfv
    wcel
    cI
    cabl
    wcel
    @0
    @2
    @1
    cR
    ringabl
    adantr
    cR
    cL
    cU
    lidlabl.l
    lidlsubg
    cU
    cR
    cI
    lidlabl.i
    subgabl
    syl2anc
end
