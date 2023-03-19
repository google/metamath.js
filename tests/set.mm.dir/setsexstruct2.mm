include "cstr.mm"
include "wbr.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cle.mm"
include "cif.mm"
include "c2nd.mm"
include "cvv.mm"
include "opex.mm"
include "a1i.mm"
include "wceq.mm"
include "eqidd.mm"
include "setsstruct2.mm"
include "mpdan.mm"
include "breq2.mm"
include "elabd.mm"

theorem setsexstruct2
  let vy: setvar y
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let cX: class X

  disjoint E y
  disjoint G y
  disjoint I y
  disjoint X y
  assert |- ( ( G Struct X /\ E e. V /\ I e. NN ) -> E. y ( G sSet <. I , E >. ) Struct y )

  proof
    cG
    cX
    cstr
    wbr
    cE
    cV
    wcel
    cI
    cn
    wcel
    w3a
    #
    cG
    cI
    cE
    cop
    csts
    co
    #
    vy
    cv
    #
    cstr
    wbr
    @1
    cI
    cX
    c1st
    cfv
    #
    cle
    wbr
    cI
    @3
    cif
    #
    cI
    cX
    c2nd
    cfv
    #
    cle
    wbr
    @5
    cI
    cif
    #
    cop
    #
    cstr
    wbr
    #
    vy
    @7
    @7
    cvv
    wcel
    @0
    @4
    @6
    opex
    a1i
    @0
    @7
    @7
    wceq
    @8
    @0
    @7
    eqidd
    cE
    cG
    cI
    cV
    cX
    @7
    setsstruct2
    mpdan
    @2
    @7
    @1
    cstr
    breq2
    elabd
end
