include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wrex.mm"
include "wn.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "cbvrexv.mm"
include "cdif.mm"
include "ntrclsrcomplex.mm"
include "adantr.mm"
include "wa.mm"
include "wceq.mm"
include "difeq2.mm"
include "adantl.mm"
include "wss.mm"
include "elpwi.mm"
include "dfss4.mm"
include "sylib.mm"
include "ad2antlr.mm"
include "eqtr2d.mm"
include "rspcedeq2vd.mm"
include "w3a.mm"
include "wb.mm"
include "3ad2ant3.mm"
include "wbr.mm"
include "simpr.mm"
include "ntrclselnel2.mm"
include "3adant3.mm"
include "bitrd.mm"
include "rexxfrd2.mm"
include "syl5bb.mm"

theorem ntrclsneine0lem
  let wph: wff ph
  let cB: class B
  let cD: class D
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cI: class I
  let cK: class K
  let cO: class O
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  assume ntrcls.o: |- O = ( i e. _V |-> ( k e. ( ~P i ^m ~P i ) |-> ( j e. ~P i |-> ( i \ ( k ` ( i \ j ) ) ) ) ) )
  assume ntrcls.d: |- D = ( O ` B )
  assume ntrcls.r: |- ( ph -> I D K )
  assume ntrclslem0.x: |- ( ph -> X e. B )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B s
  disjoint i j
  disjoint i k
  disjoint i s
  disjoint j k
  disjoint j s
  disjoint k s
  disjoint I j
  disjoint I k
  disjoint I s
  disjoint X s
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint ph s
  disjoint B t
  disjoint i t
  disjoint j t
  disjoint k t
  disjoint s t
  disjoint I t
  disjoint K t
  disjoint X t
  disjoint ph t
  assert |- ( ph -> ( E. s e. ~P B X e. ( I ` s ) <-> E. s e. ~P B -. X e. ( K ` s ) ) )

  proof
    cX
    vs
    cv
    #
    cI
    cfv
    #
    wcel
    #
    vs
    cB
    cpw
    #
    wrex
    cX
    vt
    cv
    #
    cI
    cfv
    #
    wcel
    #
    vt
    @3
    wrex
    wph
    cX
    @0
    cK
    cfv
    wcel
    wn
    #
    vs
    @3
    wrex
    @2
    @6
    vs
    vt
    @3
    vs
    vt
    weq
    @1
    @5
    cX
    @0
    @4
    cI
    fveq2
    eleq2d
    cbvrexv
    wph
    @6
    @7
    vt
    vs
    cB
    @0
    cdif
    #
    @3
    @3
    wph
    @8
    @3
    wcel
    @0
    @3
    wcel
    #
    wph
    cB
    cD
    @0
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsrcomplex
    adantr
    wph
    @4
    @3
    wcel
    #
    wa
    #
    vs
    cB
    @4
    cdif
    #
    @3
    @4
    @8
    wph
    @12
    @3
    wcel
    @10
    wph
    cB
    cD
    @4
    cI
    cK
    cO
    ntrcls.d
    ntrcls.r
    ntrclsrcomplex
    adantr
    @11
    @0
    @12
    wceq
    #
    wa
    @8
    cB
    @12
    cdif
    #
    @4
    @13
    @8
    @14
    wceq
    @11
    @0
    @12
    cB
    difeq2
    adantl
    @10
    @14
    @4
    wceq
    #
    wph
    @13
    @10
    @4
    cB
    wss
    @15
    @4
    cB
    elpwi
    @4
    cB
    dfss4
    sylib
    ad2antlr
    eqtr2d
    rspcedeq2vd
    wph
    @9
    @4
    @8
    wceq
    #
    w3a
    @6
    cX
    @8
    cI
    cfv
    #
    wcel
    #
    @7
    @16
    wph
    @6
    @18
    wb
    @9
    @16
    @5
    @17
    cX
    @4
    @8
    cI
    fveq2
    eleq2d
    3ad2ant3
    wph
    @9
    @18
    @7
    wb
    @16
    wph
    @9
    wa
    cB
    cD
    @0
    vi
    vj
    vk
    cI
    cK
    cO
    cX
    ntrcls.o
    ntrcls.d
    wph
    cI
    cK
    cD
    wbr
    @9
    ntrcls.r
    adantr
    wph
    cX
    cB
    wcel
    @9
    ntrclslem0.x
    adantr
    wph
    @9
    simpr
    ntrclselnel2
    3adant3
    bitrd
    rexxfrd2
    syl5bb
end
