include "cuspgr.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "wlknwwlksninj.mm"
include "wlknwwlksnsur.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem wlknwwlksnbij
  let vt: setvar t
  let cT: class T
  let cF: class F
  let cG: class G
  let cN: class N
  let cW: class W
  let vp: setvar p
  let vv: setvar v
  let vw: setvar w
  let vu: setvar u
  let vf: setvar f
  assume wlknwwlksnbij.t: |- T = { p e. ( Walks ` G ) | ( # ` ( 1st ` p ) ) = N }
  assume wlknwwlksnbij.w: |- W = ( N WWalksN G )
  assume wlknwwlksnbij.f: |- F = ( t e. T |-> ( 2nd ` t ) )

  disjoint G p
  disjoint G t
  disjoint p t
  disjoint N p
  disjoint N t
  disjoint T t
  disjoint W t
  disjoint F p
  disjoint T p
  disjoint W p
  disjoint F v
  disjoint F w
  disjoint v w
  disjoint G v
  disjoint G w
  disjoint p v
  disjoint p w
  disjoint t v
  disjoint t w
  disjoint N v
  disjoint N w
  disjoint T v
  disjoint T w
  disjoint F u
  disjoint p u
  disjoint G f
  disjoint G u
  disjoint f p
  disjoint f u
  disjoint N f
  disjoint N u
  disjoint T u
  disjoint t u
  disjoint W u
  assert |- ( ( G e. USPGraph /\ N e. NN0 ) -> F : T -1-1-onto-> W )

  proof
    cG
    cuspgr
    wcel
    cN
    cn0
    wcel
    wa
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
    vt
    cT
    cF
    cG
    cN
    cW
    vp
    wlknwwlksnbij.t
    wlknwwlksnbij.w
    wlknwwlksnbij.f
    wlknwwlksninj
    vt
    cT
    cF
    cG
    cN
    cW
    vp
    wlknwwlksnbij.t
    wlknwwlksnbij.w
    wlknwwlksnbij.f
    wlknwwlksnsur
    cT
    cW
    cF
    df-f1o
    sylanbrc
end
