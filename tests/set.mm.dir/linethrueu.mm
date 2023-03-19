include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "clines2.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "hilbert1.1.mm"
include "simpr3.mm"
include "hilbert1.2.mm"
include "syl.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem linethrueu
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let cN: class N

  disjoint P x
  disjoint Q x
  assert |- ( ( N e. NN /\ ( P e. ( EE ` N ) /\ Q e. ( EE ` N ) /\ P =/= Q ) ) -> E! x e. LinesEE ( P e. x /\ Q e. x ) )

  proof
    cN
    cn
    wcel
    #
    cP
    cN
    cee
    cfv
    #
    wcel
    #
    cQ
    @1
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    wa
    #
    cP
    vx
    cv
    #
    wcel
    cQ
    @6
    wcel
    wa
    #
    vx
    clines2
    wrex
    @7
    vx
    clines2
    wrmo
    #
    @7
    vx
    clines2
    wreu
    vx
    cP
    cQ
    cN
    hilbert1.1
    @5
    @4
    @8
    @0
    @2
    @3
    @4
    simpr3
    vx
    cP
    cQ
    hilbert1.2
    syl
    @7
    vx
    clines2
    reu5
    sylanbrc
end
