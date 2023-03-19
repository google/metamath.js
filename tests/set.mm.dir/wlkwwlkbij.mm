include "cuspgr.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "wlkwwlkinj.mm"
include "wlkwwlksur.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem wlkwwlkbij
  let vw: setvar w
  let vt: setvar t
  let cP: class P
  let cT: class T
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  assume wlkwwlkbij.t: |- T = { p e. ( Walks ` G ) | ( ( # ` ( 1st ` p ) ) = N /\ ( ( 2nd ` p ) ` 0 ) = P ) }
  assume wlkwwlkbij.w: |- W = { w e. ( N WWalksN G ) | ( w ` 0 ) = P }
  assume wlkwwlkbij.f: |- F = ( t e. T |-> ( 2nd ` t ) )

  disjoint G p
  disjoint G t
  disjoint G w
  disjoint p t
  disjoint p w
  disjoint t w
  disjoint N p
  disjoint N t
  disjoint N w
  disjoint P p
  disjoint P t
  disjoint P w
  disjoint T t
  disjoint T w
  disjoint V t
  disjoint W t
  disjoint F w
  disjoint V w
  disjoint F p
  disjoint T p
  disjoint W p
  disjoint F v
  disjoint v w
  disjoint G v
  disjoint p v
  disjoint N v
  disjoint P v
  disjoint T v
  disjoint t v
  disjoint V v
  disjoint F u
  disjoint p u
  disjoint G f
  disjoint G u
  disjoint f p
  disjoint f u
  disjoint f w
  disjoint u w
  disjoint N f
  disjoint N u
  disjoint P f
  disjoint P u
  disjoint T u
  disjoint t u
  disjoint W u
  assert |- ( ( G e. USPGraph /\ P e. V /\ N e. NN0 ) -> F : T -1-1-onto-> W )

  proof
    cG
    cuspgr
    wcel
    cP
    cV
    wcel
    cN
    cn0
    wcel
    w3a
    cT
    cW
    cF
    wf1
    cT
    cW
    cF
    wfo
    cT
    cW
    cF
    wf1o
    vw
    vt
    cP
    cT
    cF
    cG
    cN
    cV
    cW
    vp
    wlkwwlkbij.t
    wlkwwlkbij.w
    wlkwwlkbij.f
    wlkwwlkinj
    vw
    vt
    cP
    cT
    cF
    cG
    cN
    cV
    cW
    vp
    wlkwwlkbij.t
    wlkwwlkbij.w
    wlkwwlkbij.f
    wlkwwlksur
    cT
    cW
    cF
    df-f1o
    sylanbrc
end
