include "cuo.mm"
include "wcel.mm"
include "clo.mm"
include "cnop.mm"
include "cfv.mm"
include "cr.mm"
include "cbo.mm"
include "unoplin.mm"
include "chil.mm"
include "c0h.mm"
include "wceq.mm"
include "wf.mm"
include "wf1o.mm"
include "unopf1o.mm"
include "f1of.mm"
include "syl.mm"
include "wa.mm"
include "cc0.mm"
include "nmop0h.mm"
include "0re.mm"
include "syl6eqel.mm"
include "sylan2.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "c1.mm"
include "nmopun.mm"
include "1re.mm"
include "sylanbr.mm"
include "pm2.61ian.mm"
include "elbdop2.mm"
include "sylanbrc.mm"

theorem unopbd
  let cT: class T


  assert |- ( T e. UniOp -> T e. BndLinOp )

  proof
    cT
    cuo
    wcel
    #
    cT
    clo
    wcel
    cT
    cnop
    cfv
    #
    cr
    wcel
    #
    cT
    cbo
    wcel
    cT
    unoplin
    chil
    c0h
    wceq
    #
    @0
    @2
    @0
    @3
    chil
    chil
    cT
    wf
    #
    @2
    @0
    chil
    chil
    cT
    wf1o
    @4
    cT
    unopf1o
    chil
    chil
    cT
    f1of
    syl
    @3
    @4
    wa
    @1
    cc0
    cr
    cT
    nmop0h
    0re
    syl6eqel
    sylan2
    @3
    wn
    chil
    c0h
    wne
    #
    @0
    @2
    chil
    c0h
    df-ne
    @5
    @0
    wa
    @1
    c1
    cr
    cT
    nmopun
    1re
    syl6eqel
    sylanbr
    pm2.61ian
    cT
    elbdop2
    sylanbrc
end
