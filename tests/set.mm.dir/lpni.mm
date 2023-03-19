include "cplig.mm"
include "wcel.mm"
include "cv.mm"
include "wnel.mm"
include "wrex.mm"
include "w3a.mm"
include "wn.mm"
include "wral.mm"
include "wi.mm"
include "tncp.mm"
include "wa.mm"
include "wceq.mm"
include "eleq2.mm"
include "3anbi123d.mm"
include "notbid.mm"
include "rspccv.mm"
include "w3o.mm"
include "weq.mm"
include "eleq1.mm"
include "rspcev.mm"
include "ex.mm"
include "3jaao.mm"
include "3ianor.mm"
include "df-nel.mm"
include "rexbii.mm"
include "3imtr4g.mm"
include "syl9r.mm"
include "3expia.mm"
include "rexlimdv.mm"
include "rexlimivv.mm"
include "syl.mm"
include "imp.mm"

theorem lpni
  let cP: class P
  let cG: class G
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vl: setvar l
  let vd: setvar d
  assume l2p.1: |- P = U. G

  disjoint G a
  disjoint L a
  disjoint P a
  disjoint a b
  disjoint a c
  disjoint a l
  disjoint b c
  disjoint b l
  disjoint G b
  disjoint c l
  disjoint G c
  disjoint G l
  disjoint L b
  disjoint L l
  disjoint P b
  disjoint P c
  disjoint P l
  disjoint G d
  disjoint a d
  disjoint b d
  disjoint c d
  disjoint L c
  disjoint d l
  disjoint L d
  disjoint P d
  assert |- ( ( G e. Plig /\ L e. G ) -> E. a e. P a e/ L )

  proof
    cG
    cplig
    wcel
    #
    cL
    cG
    wcel
    #
    va
    cv
    #
    cL
    wnel
    #
    va
    cP
    wrex
    #
    @0
    vb
    cv
    #
    vl
    cv
    #
    wcel
    #
    vc
    cv
    #
    @6
    wcel
    #
    vd
    cv
    #
    @6
    wcel
    #
    w3a
    #
    wn
    #
    vl
    cG
    wral
    #
    vd
    cP
    wrex
    #
    vc
    cP
    wrex
    vb
    cP
    wrex
    @1
    @4
    wi
    #
    cP
    cG
    vb
    vc
    vd
    vl
    l2p.1
    tncp
    @15
    @16
    vb
    vc
    cP
    cP
    @5
    cP
    wcel
    #
    @8
    cP
    wcel
    #
    wa
    @14
    @16
    vd
    cP
    @17
    @18
    @10
    cP
    wcel
    #
    @14
    @16
    wi
    @14
    @1
    @5
    cL
    wcel
    #
    @8
    cL
    wcel
    #
    @10
    cL
    wcel
    #
    w3a
    #
    wn
    #
    @17
    @18
    @19
    w3a
    #
    @4
    @13
    @24
    vl
    cL
    cG
    @6
    cL
    wceq
    #
    @12
    @23
    @26
    @7
    @20
    @9
    @21
    @11
    @22
    @6
    cL
    @5
    eleq2
    @6
    cL
    @8
    eleq2
    @6
    cL
    @10
    eleq2
    3anbi123d
    notbid
    rspccv
    @25
    @20
    wn
    #
    @21
    wn
    #
    @22
    wn
    #
    w3o
    @2
    cL
    wcel
    #
    wn
    #
    va
    cP
    wrex
    #
    @24
    @4
    @17
    @27
    @32
    @18
    @28
    @19
    @29
    @17
    @27
    @32
    @31
    @27
    va
    @5
    cP
    va
    vb
    weq
    @30
    @20
    @2
    @5
    cL
    eleq1
    notbid
    rspcev
    ex
    @18
    @28
    @32
    @31
    @28
    va
    @8
    cP
    va
    vc
    weq
    @30
    @21
    @2
    @8
    cL
    eleq1
    notbid
    rspcev
    ex
    @19
    @29
    @32
    @31
    @29
    va
    @10
    cP
    va
    vd
    weq
    @30
    @22
    @2
    @10
    cL
    eleq1
    notbid
    rspcev
    ex
    3jaao
    @20
    @21
    @22
    3ianor
    @3
    @31
    va
    cP
    @2
    cL
    df-nel
    rexbii
    3imtr4g
    syl9r
    3expia
    rexlimdv
    rexlimivv
    syl
    imp
end
