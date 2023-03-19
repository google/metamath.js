include "com.mm"
include "cuz.mm"
include "cfv.mm"
include "wf1o.mm"
include "wf1.mm"
include "crn.mm"
include "wceq.mm"
include "wf.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wfn.mm"
include "wss.mm"
include "cvv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "crdg.mm"
include "cres.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "om2uzrani.mm"
include "eqimssi.mm"
include "df-f.mm"
include "mpbir2an.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "wn.mm"
include "cr.mm"
include "wb.mm"
include "cz.mm"
include "om2uzuzi.mm"
include "eluzelz.mm"
include "syl.mm"
include "zred.mm"
include "lttri3.mm"
include "syl2an.mm"
include "ioran.mm"
include "syl6bbr.mm"
include "word.mm"
include "nnord.mm"
include "ordtri3.mm"
include "con2bid.mm"
include "om2uzlti.mm"
include "ancoms.mm"
include "orim12d.mm"
include "sylbird.mm"
include "con1d.mm"
include "sylbid.mm"
include "rgen2a.mm"
include "dff13.mm"
include "dff1o5.mm"

theorem om2uzf1oi
  let vx: setvar x
  let cC: class C
  let cG: class G
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let cB: class B
  let vv: setvar v
  assume om2uz.1: |- C e. ZZ
  assume om2uz.2: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , C ) |` _om )

  disjoint C x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C y
  disjoint C z
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint G z
  assert |- G : _om -1-1-onto-> ( ZZ>= ` C )

  proof
    com
    cC
    cuz
    cfv
    #
    cG
    wf1o
    com
    @0
    cG
    wf1
    #
    cG
    crn
    #
    @0
    wceq
    @1
    com
    @0
    cG
    wf
    #
    vy
    cv
    #
    cG
    cfv
    #
    vz
    cv
    #
    cG
    cfv
    #
    wceq
    #
    @4
    @6
    wceq
    #
    wi
    #
    vz
    com
    wral
    vy
    com
    wral
    @3
    cG
    com
    wfn
    #
    @2
    @0
    wss
    @11
    vx
    cvv
    vx
    cv
    c1
    caddc
    co
    cmpt
    #
    cC
    crdg
    com
    cres
    #
    com
    wfn
    cC
    @12
    frfnom
    com
    cG
    @13
    om2uz.2
    fneq1i
    mpbir
    @2
    @0
    vx
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzrani
    #
    eqimssi
    com
    @0
    cG
    df-f
    mpbir2an
    @10
    vy
    vz
    com
    @4
    com
    wcel
    #
    @6
    com
    wcel
    #
    wa
    #
    @8
    @5
    @7
    clt
    wbr
    #
    @7
    @5
    clt
    wbr
    #
    wo
    #
    wn
    #
    @9
    @17
    @8
    @18
    wn
    @19
    wn
    wa
    #
    @21
    @15
    @5
    cr
    wcel
    @7
    cr
    wcel
    @8
    @22
    wb
    @16
    @15
    @5
    @15
    @5
    @0
    wcel
    @5
    cz
    wcel
    vx
    @4
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzuzi
    cC
    @5
    eluzelz
    syl
    zred
    @16
    @7
    @16
    @7
    @0
    wcel
    @7
    cz
    wcel
    vx
    @6
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzuzi
    cC
    @7
    eluzelz
    syl
    zred
    @5
    @7
    lttri3
    syl2an
    @18
    @19
    ioran
    syl6bbr
    @17
    @9
    @20
    @17
    @9
    wn
    @4
    @6
    wcel
    #
    @6
    @4
    wcel
    #
    wo
    #
    @20
    @17
    @9
    @25
    @15
    @4
    word
    @6
    word
    @9
    @25
    wn
    wb
    @16
    @4
    nnord
    @6
    nnord
    @4
    @6
    ordtri3
    syl2an
    con2bid
    @17
    @23
    @18
    @24
    @19
    vx
    @4
    @6
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzlti
    @16
    @15
    @24
    @19
    wi
    vx
    @6
    @4
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzlti
    ancoms
    orim12d
    sylbird
    con1d
    sylbid
    rgen2a
    vy
    vz
    com
    @0
    cG
    dff13
    mpbir2an
    @14
    com
    @0
    cG
    dff1o5
    mpbir2an
end
