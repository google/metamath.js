include "wf.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "w3a.mm"
include "csn.mm"
include "cun.mm"
include "cop.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "simp1.mm"
include "wf1o.mm"
include "simp2l.mm"
include "simp3.mm"
include "f1osng.mm"
include "syl2anc.mm"
include "f1of.mm"
include "syl.mm"
include "simp2r.mm"
include "disjsn.mm"
include "sylibr.mm"
include "fun.mm"
include "syl21anc.mm"
include "wss.mm"
include "snssi.mm"
include "3ad2ant3.mm"
include "ssequn2.mm"
include "sylib.mm"
include "feq3d.mm"
include "mpbid.mm"

theorem fsnunf
  let cS: class S
  let cT: class T
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( F : S --> T /\ ( X e. V /\ -. X e. S ) /\ Y e. T ) -> ( F u. { <. X , Y >. } ) : ( S u. { X } ) --> T )

  proof
    cS
    cT
    cF
    wf
    #
    cX
    cV
    wcel
    #
    cX
    cS
    wcel
    wn
    #
    wa
    #
    cY
    cT
    wcel
    #
    w3a
    #
    cS
    cX
    csn
    #
    cun
    #
    cT
    cY
    csn
    #
    cun
    #
    cF
    cX
    cY
    cop
    csn
    #
    cun
    #
    wf
    #
    @7
    cT
    @11
    wf
    @5
    @0
    @6
    @8
    @10
    wf
    #
    cS
    @6
    cin
    c0
    wceq
    #
    @12
    @0
    @3
    @4
    simp1
    @5
    @6
    @8
    @10
    wf1o
    #
    @13
    @5
    @1
    @4
    @15
    @0
    @1
    @2
    @4
    simp2l
    @0
    @3
    @4
    simp3
    cX
    cY
    cV
    cT
    f1osng
    syl2anc
    @6
    @8
    @10
    f1of
    syl
    @5
    @2
    @14
    @0
    @1
    @2
    @4
    simp2r
    cS
    cX
    disjsn
    sylibr
    cS
    @6
    cT
    @8
    cF
    @10
    fun
    syl21anc
    @5
    @9
    cT
    @11
    @7
    @5
    @8
    cT
    wss
    #
    @9
    cT
    wceq
    @4
    @0
    @16
    @3
    cY
    cT
    snssi
    3ad2ant3
    @8
    cT
    ssequn2
    sylib
    feq3d
    mpbid
end
