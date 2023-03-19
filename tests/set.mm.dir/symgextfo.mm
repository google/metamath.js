include "wcel.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "symgextf.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "wf1o.mm"
include "csymg.mm"
include "eqid.mm"
include "symgbasf1o.mm"
include "f1ofo.mm"
include "syl.mm"
include "adantl.mm"
include "dffo3.mm"
include "sylib.mm"
include "simprd.mm"
include "symgextfv.mm"
include "imp.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "mpbird.mm"
include "wss.mm"
include "wi.mm"
include "difssd.mm"
include "ssrexv.mm"
include "ralimia.mm"
include "simpl.mm"
include "symgextfve.mm"
include "adantr.mm"
include "eqcomd.mm"
include "rspcedeq2vd.mm"
include "wb.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "ralunsn.mm"
include "mpbir2and.mm"
include "difsnid.mm"
include "raleqdv.mm"
include "sylanbrc.mm"

theorem symgextfo
  let vx: setvar x
  let cS: class S
  let cE: class E
  let cK: class K
  let cN: class N
  let cZ: class Z
  let cX: class X
  let cY: class Y
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume symgext.s: |- S = ( Base ` ( SymGrp ` ( N \ { K } ) ) )
  assume symgext.e: |- E = ( x e. N |-> if ( x = K , K , ( Z ` x ) ) )

  disjoint K x
  disjoint N x
  disjoint S x
  disjoint Z x
  disjoint X x
  disjoint Y x
  disjoint E y
  disjoint E z
  disjoint y z
  disjoint K i
  disjoint K j
  disjoint K y
  disjoint i j
  disjoint i y
  disjoint j y
  disjoint K z
  disjoint N i
  disjoint N j
  disjoint N y
  disjoint N z
  disjoint S y
  disjoint S z
  disjoint Z i
  disjoint Z j
  disjoint Z y
  disjoint Z z
  disjoint x y
  disjoint x z
  disjoint j z
  disjoint E i
  disjoint E k
  disjoint i k
  disjoint K k
  disjoint N k
  disjoint S i
  disjoint S k
  disjoint Z k
  disjoint i x
  assert |- ( ( K e. N /\ Z e. S ) -> E : N -onto-> N )

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
    cN
    cN
    cE
    wf
    vk
    cv
    #
    vi
    cv
    #
    cE
    cfv
    #
    wceq
    #
    vi
    cN
    wrex
    #
    vk
    cN
    wral
    #
    cN
    cN
    cE
    wfo
    vx
    cS
    cE
    cK
    cN
    cZ
    symgext.s
    symgext.e
    symgextf
    @2
    @8
    @7
    vk
    cN
    cK
    csn
    #
    cdif
    #
    @9
    cun
    #
    wral
    #
    @2
    @12
    @7
    vk
    @10
    wral
    #
    cK
    @5
    wceq
    #
    vi
    cN
    wrex
    #
    @2
    @6
    vi
    @10
    wrex
    #
    vk
    @10
    wral
    #
    @13
    @2
    @17
    @3
    @4
    cZ
    cfv
    #
    wceq
    #
    vi
    @10
    wrex
    #
    vk
    @10
    wral
    #
    @2
    @10
    @10
    cZ
    wf
    #
    @21
    @2
    @10
    @10
    cZ
    wfo
    #
    @22
    @21
    wa
    @1
    @23
    @0
    @1
    @10
    @10
    cZ
    wf1o
    @23
    @10
    cS
    cZ
    @10
    csymg
    cfv
    #
    @24
    eqid
    symgext.s
    symgbasf1o
    @10
    @10
    cZ
    f1ofo
    syl
    adantl
    vi
    vk
    @10
    @10
    cZ
    dffo3
    sylib
    simprd
    @2
    @16
    @20
    vk
    @10
    @2
    @6
    @19
    vi
    @10
    @2
    @4
    @10
    wcel
    #
    wa
    @5
    @18
    @3
    @2
    @25
    @5
    @18
    wceq
    vx
    cS
    cE
    cK
    cN
    @4
    cZ
    symgext.s
    symgext.e
    symgextfv
    imp
    eqeq2d
    rexbidva
    ralbidv
    mpbird
    @16
    @7
    vk
    @10
    @3
    @10
    wcel
    #
    @10
    cN
    wss
    @16
    @7
    wi
    @26
    cN
    @9
    difssd
    @6
    vi
    @10
    cN
    ssrexv
    syl
    ralimia
    syl
    @2
    vi
    cK
    cN
    cK
    @5
    @0
    @1
    simpl
    @2
    @4
    cK
    wceq
    #
    wa
    @5
    cK
    @2
    @27
    @5
    cK
    wceq
    #
    @0
    @27
    @28
    wi
    @1
    vx
    cS
    cE
    cK
    cN
    @4
    cZ
    symgext.s
    symgext.e
    symgextfve
    adantr
    imp
    eqcomd
    rspcedeq2vd
    @0
    @12
    @13
    @15
    wa
    wb
    @1
    @7
    @15
    vk
    @10
    cK
    cN
    @3
    cK
    wceq
    @6
    @14
    vi
    cN
    @3
    cK
    @5
    eqeq1
    rexbidv
    ralunsn
    adantr
    mpbir2and
    @0
    @8
    @12
    wb
    @1
    @0
    @7
    vk
    cN
    @11
    @0
    @11
    cN
    cN
    cK
    difsnid
    eqcomd
    raleqdv
    adantr
    mpbird
    vi
    vk
    cN
    cN
    cE
    dffo3
    sylanbrc
end
