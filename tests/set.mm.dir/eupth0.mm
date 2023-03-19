include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "csn.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "cfzo.mm"
include "co.mm"
include "cdm.mm"
include "wf1o.mm"
include "ceupth.mm"
include "eqidd.mm"
include "is0wlk.mm"
include "mpancom.mm"
include "f1o0.mm"
include "hash0.mm"
include "oveq2i.mm"
include "fzo0.mm"
include "eqtri.mm"
include "a1i.mm"
include "dmeq.mm"
include "dm0.mm"
include "syl6eq.mm"
include "f1oeq123d.mm"
include "mpbiri.mm"
include "anim12i.mm"
include "iseupthf1o.mm"
include "sylibr.mm"

theorem eupth0
  let cA: class A
  let cG: class G
  let cI: class I
  let cV: class V
  assume eupth0.v: |- V = ( Vtx ` G )
  assume eupth0.i: |- I = ( iEdg ` G )


  assert |- ( ( A e. V /\ I = (/) ) -> (/) ( EulerPaths ` G ) { <. 0 , A >. } )

  proof
    cA
    cV
    wcel
    #
    cI
    c0
    wceq
    #
    wa
    c0
    cc0
    cA
    cop
    csn
    #
    cG
    cwlks
    cfv
    wbr
    #
    cc0
    c0
    chash
    cfv
    #
    cfzo
    co
    #
    cI
    cdm
    #
    c0
    wf1o
    #
    wa
    c0
    @2
    cG
    ceupth
    cfv
    wbr
    @0
    @3
    @1
    @7
    @2
    @2
    wceq
    @0
    @3
    @0
    @2
    eqidd
    @2
    cG
    cA
    cV
    eupth0.v
    is0wlk
    mpancom
    @1
    @7
    c0
    c0
    c0
    wf1o
    f1o0
    @1
    @5
    c0
    @6
    c0
    c0
    c0
    @1
    c0
    eqidd
    @5
    c0
    wceq
    @1
    @5
    cc0
    cc0
    cfzo
    co
    c0
    @4
    cc0
    cc0
    cfzo
    hash0
    oveq2i
    cc0
    fzo0
    eqtri
    a1i
    @1
    @6
    c0
    cdm
    c0
    cI
    c0
    dmeq
    dm0
    syl6eq
    f1oeq123d
    mpbiri
    anim12i
    @2
    c0
    cG
    cI
    eupth0.i
    iseupthf1o
    sylibr
end
