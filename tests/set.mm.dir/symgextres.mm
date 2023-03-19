include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "symgextfv.mm"
include "ralrimiv.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "wf.mm"
include "symgextf.mm"
include "ffn.mm"
include "syl.mm"
include "csymg.mm"
include "eqid.mm"
include "symgbasf.mm"
include "adantl.mm"
include "difssd.mm"
include "fvreseq1.mm"
include "syl21anc.mm"
include "mpbird.mm"

theorem symgextres
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
  assert |- ( ( K e. N /\ Z e. S ) -> ( E |` ( N \ { K } ) ) = Z )

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
    cE
    cN
    cK
    csn
    #
    cdif
    #
    cres
    cZ
    wceq
    #
    vi
    cv
    #
    cE
    cfv
    @6
    cZ
    cfv
    wceq
    #
    vi
    @4
    wral
    #
    @2
    @7
    vi
    @4
    vx
    cS
    cE
    cK
    cN
    @6
    cZ
    symgext.s
    symgext.e
    symgextfv
    ralrimiv
    @2
    cE
    cN
    wfn
    #
    cZ
    @4
    wfn
    #
    @4
    cN
    wss
    @5
    @8
    wb
    @2
    cN
    cN
    cE
    wf
    @9
    vx
    cS
    cE
    cK
    cN
    cZ
    symgext.s
    symgext.e
    symgextf
    cN
    cN
    cE
    ffn
    syl
    @1
    @10
    @0
    @1
    @4
    @4
    cZ
    wf
    @10
    @4
    cS
    cZ
    @4
    csymg
    cfv
    #
    @11
    eqid
    symgext.s
    symgbasf
    @4
    @4
    cZ
    ffn
    syl
    adantl
    @2
    cN
    @3
    difssd
    vi
    cN
    @4
    cE
    cZ
    fvreseq1
    syl21anc
    mpbird
end
