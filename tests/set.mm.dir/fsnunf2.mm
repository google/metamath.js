include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "wcel.mm"
include "w3a.mm"
include "cun.mm"
include "cop.mm"
include "wn.mm"
include "simp1.mm"
include "simp2.mm"
include "neldifsnd.mm"
include "simp3.mm"
include "fsnunf.mm"
include "syl121anc.mm"
include "wceq.mm"
include "difsnid.mm"
include "3ad2ant2.mm"
include "feq2d.mm"
include "mpbid.mm"

theorem fsnunf2
  let cS: class S
  let cT: class T
  let cF: class F
  let cX: class X
  let cY: class Y


  assert |- ( ( F : ( S \ { X } ) --> T /\ X e. S /\ Y e. T ) -> ( F u. { <. X , Y >. } ) : S --> T )

  proof
    cS
    cX
    csn
    #
    cdif
    #
    cT
    cF
    wf
    #
    cX
    cS
    wcel
    #
    cY
    cT
    wcel
    #
    w3a
    #
    @1
    @0
    cun
    #
    cT
    cF
    cX
    cY
    cop
    csn
    cun
    #
    wf
    #
    cS
    cT
    @7
    wf
    @5
    @2
    @3
    cX
    @1
    wcel
    wn
    @4
    @8
    @2
    @3
    @4
    simp1
    @2
    @3
    @4
    simp2
    @5
    cX
    cS
    neldifsnd
    @2
    @3
    @4
    simp3
    @1
    cT
    cF
    cS
    cX
    cY
    fsnunf
    syl121anc
    @5
    @6
    cS
    cT
    @7
    @3
    @2
    @6
    cS
    wceq
    @4
    cS
    cX
    difsnid
    3ad2ant2
    feq2d
    mpbid
end
