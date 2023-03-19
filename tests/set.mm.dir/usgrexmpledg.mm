include "cedg.mm"
include "cfv.mm"
include "ciedg.mm"
include "crn.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "c2.mm"
include "c3.mm"
include "cun.mm"
include "edgval.mm"
include "cvtx.mm"
include "wceq.mm"
include "usgrexmpllem.mm"
include "simpri.mm"
include "rneqi.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cs4.mm"
include "cdm.mm"
include "wf1o.mm"
include "prex.mm"
include "pm3.2i.mm"
include "usgrexmpldifpr.mm"
include "s4f1o.mm"
include "imp31.mm"
include "wf1.mm"
include "dff1o5.mm"
include "simprbi.mm"
include "mp2b.mm"
include "3eqtri.mm"

theorem usgrexmpledg
  let cE: class E
  let cG: class G
  let cV: class V
  assume usgrexmpl.v: |- V = ( 0 ... 4 )
  assume usgrexmpl.e: |- E = <" { 0 , 1 } { 1 , 2 } { 2 , 0 } { 0 , 3 } ">
  assume usgrexmpl.g: |- G = <. V , E >.


  assert |- ( Edg ` G ) = ( { { 0 , 1 } , { 1 , 2 } } u. { { 2 , 0 } , { 0 , 3 } } )

  proof
    cG
    cedg
    cfv
    cG
    ciedg
    cfv
    #
    crn
    cE
    crn
    #
    cc0
    c1
    cpr
    #
    c1
    c2
    cpr
    #
    cpr
    c2
    cc0
    cpr
    #
    cc0
    c3
    cpr
    #
    cpr
    cun
    #
    cG
    edgval
    @0
    cE
    cG
    cvtx
    cfv
    cV
    wceq
    @0
    cE
    wceq
    cE
    cG
    cV
    usgrexmpl.v
    usgrexmpl.e
    usgrexmpl.g
    usgrexmpllem
    simpri
    rneqi
    @2
    cvv
    wcel
    #
    @3
    cvv
    wcel
    #
    wa
    #
    @4
    cvv
    wcel
    #
    @5
    cvv
    wcel
    #
    wa
    #
    wa
    #
    @2
    @3
    wne
    @2
    @4
    wne
    @2
    @5
    wne
    w3a
    @3
    @4
    wne
    @3
    @5
    wne
    @4
    @5
    wne
    w3a
    wa
    #
    wa
    #
    cE
    @2
    @3
    @4
    @5
    cs4
    wceq
    #
    wa
    cE
    cdm
    #
    @6
    cE
    wf1o
    #
    @1
    @6
    wceq
    #
    @15
    @16
    @13
    @14
    @9
    @12
    @7
    @8
    cc0
    c1
    prex
    c1
    c2
    prex
    pm3.2i
    @10
    @11
    c2
    cc0
    prex
    cc0
    c3
    prex
    pm3.2i
    pm3.2i
    usgrexmpldifpr
    pm3.2i
    usgrexmpl.e
    pm3.2i
    @13
    @14
    @16
    @18
    @2
    @3
    @4
    @5
    cvv
    cE
    s4f1o
    imp31
    @18
    @17
    @6
    cE
    wf1
    @19
    @17
    @6
    cE
    dff1o5
    simprbi
    mp2b
    3eqtri
end
