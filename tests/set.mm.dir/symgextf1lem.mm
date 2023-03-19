include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "wne.mm"
include "csymg.mm"
include "eqid.mm"
include "symgfv.mm"
include "adantll.mm"
include "eldifsni.mm"
include "wceq.mm"
include "symgextfv.mm"
include "imp.mm"
include "neeq1d.mm"
include "syl5ibr.mm"
include "mpd.mm"
include "adantrr.mm"
include "wi.mm"
include "elsni.mm"
include "symgextfve.mm"
include "adantr.mm"
include "syl5com.mm"
include "adantl.mm"
include "impcom.mm"
include "neeqtrrd.mm"
include "ex.mm"

theorem symgextf1lem
  let vx: setvar x
  let cS: class S
  let cE: class E
  let cK: class K
  let cN: class N
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume symgext.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgext.e: |- E = ( x e. N |-> if ( x = K , K , ( Z ` x ) ) )

  disjoint K x
  disjoint N x
  disjoint S x
  disjoint Z x
  disjoint X x
  disjoint Y x
  assert |- ( ( K e. N /\ Z e. S ) -> ( ( X e. ( N \ { K } ) /\ Y e. { K } ) -> ( E ` X ) =/= ( E ` Y ) ) )

  proof
    cK
    cN
    wcel
    #
    cZ
    cS
    wcel
    #
    wa
    #
    cX
    cN
    cK
    csn
    #
    cdif
    #
    wcel
    #
    cY
    @3
    wcel
    #
    wa
    #
    cX
    cE
    cfv
    #
    cY
    cE
    cfv
    #
    wne
    @2
    @7
    wa
    @8
    cK
    @9
    @2
    @5
    @8
    cK
    wne
    #
    @6
    @2
    @5
    wa
    #
    cX
    cZ
    cfv
    #
    @4
    wcel
    #
    @10
    @1
    @5
    @13
    @0
    @4
    cS
    cZ
    @4
    csymg
    cfv
    #
    cX
    @14
    eqid
    symgext.s
    symgfv
    adantll
    @13
    @10
    @11
    @12
    cK
    wne
    @12
    cN
    cK
    eldifsni
    @11
    @8
    @12
    cK
    @2
    @5
    @8
    @12
    wceq
    vx
    cS
    cE
    cK
    cN
    cX
    cZ
    symgext.s
    symgext.e
    symgextfv
    imp
    neeq1d
    syl5ibr
    mpd
    adantrr
    @7
    @2
    @9
    cK
    wceq
    #
    @6
    @2
    @15
    wi
    @5
    @6
    cY
    cK
    wceq
    #
    @2
    @15
    cY
    cK
    elsni
    @0
    @16
    @15
    wi
    @1
    vx
    cS
    cE
    cK
    cN
    cY
    cZ
    symgext.s
    symgext.e
    symgextfve
    adantr
    syl5com
    adantl
    impcom
    neeqtrrd
    ex
end
