include "cusgr.mm"
include "wcel.mm"
include "ccusgr.mm"
include "wa.mm"
include "wss.mm"
include "weq.mm"
include "wrex.mm"
include "wral.mm"
include "usgredgsscusgredg.mm"
include "dfss5.mm"
include "sylib.mm"

theorem usgrsscusgr
  let ve: setvar e
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vn: setvar n
  assume fusgrmaxsize.v: |- V = ( Vtx ` G )
  assume fusgrmaxsize.e: |- E = ( Edg ` G )
  assume usgrsscusgra.h: |- V = ( Vtx ` H )
  assume usgrsscusgra.f: |- F = ( Edg ` H )

  disjoint F e
  disjoint F f
  disjoint e f
  disjoint H e
  disjoint E e
  disjoint G e
  disjoint F a
  disjoint F b
  disjoint F k
  disjoint F n
  disjoint a b
  disjoint a e
  disjoint a f
  disjoint a k
  disjoint a n
  disjoint b e
  disjoint b f
  disjoint b k
  disjoint b n
  disjoint e k
  disjoint e n
  disjoint f k
  disjoint f n
  disjoint k n
  disjoint G a
  disjoint G b
  disjoint H a
  disjoint H b
  disjoint H k
  disjoint H n
  disjoint V a
  disjoint V b
  disjoint V k
  disjoint V n
  assert |- ( ( G e. USGraph /\ H e. ComplUSGraph ) -> A. e e. E E. f e. F e = f )

  proof
    cG
    cusgr
    wcel
    cH
    ccusgr
    wcel
    wa
    cE
    cF
    wss
    ve
    vf
    weq
    vf
    cF
    wrex
    ve
    cE
    wral
    cE
    cF
    cG
    cH
    cV
    fusgrmaxsize.v
    fusgrmaxsize.e
    usgrsscusgra.h
    usgrsscusgra.f
    usgredgsscusgredg
    ve
    vf
    cE
    cF
    dfss5
    sylib
end
