include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "simpl.mm"
include "resubcl.mm"
include "3adant3.mm"
include "simp3.mm"
include "resubcld.mm"
include "adantl.mm"
include "simpr2.mm"
include "ltadd1d.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "nnpcan.mm"
include "syl3an.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem ltsubsubaddltsub
  let cJ: class J
  let cL: class L
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( J e. RR /\ ( L e. RR /\ M e. RR /\ N e. RR ) ) -> ( J < ( ( L - M ) - N ) <-> ( J + M ) < ( L - N ) ) )

  proof
    cJ
    cr
    wcel
    #
    cL
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    w3a
    #
    wa
    #
    cJ
    cL
    cM
    cmin
    co
    #
    cN
    cmin
    co
    #
    clt
    wbr
    cJ
    cM
    caddc
    co
    #
    @7
    cM
    caddc
    co
    #
    clt
    wbr
    @8
    cL
    cN
    cmin
    co
    #
    clt
    wbr
    @5
    cJ
    @7
    cM
    @0
    @4
    simpl
    @4
    @7
    cr
    wcel
    @0
    @4
    @6
    cN
    @1
    @2
    @6
    cr
    wcel
    @3
    cL
    cM
    resubcl
    3adant3
    @1
    @2
    @3
    simp3
    resubcld
    adantl
    @0
    @1
    @2
    @3
    simpr2
    ltadd1d
    @5
    @9
    @10
    @8
    clt
    @4
    @9
    @10
    wceq
    #
    @0
    @1
    cL
    cc
    wcel
    @2
    cM
    cc
    wcel
    @3
    cN
    cc
    wcel
    @11
    cL
    recn
    cM
    recn
    cN
    recn
    cL
    cM
    cN
    nnpcan
    syl3an
    adantl
    breq2d
    bitrd
end
