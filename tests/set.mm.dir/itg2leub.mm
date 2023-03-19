include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "citg2.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cofr.mm"
include "citg1.mm"
include "wceq.mm"
include "cdm.mm"
include "wrex.mm"
include "cab.mm"
include "clt.mm"
include "csup.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "itg2val.mm"
include "adantr.mm"
include "breq1d.mm"
include "wb.mm"
include "wss.mm"
include "itg2lcl.mm"
include "supxrleub.mm"
include "mpan.mm"
include "adantl.mm"
include "wal.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "ralab.mm"
include "r19.23v.mm"
include "ancomst.mm"
include "impexp.mm"
include "bitri.mm"
include "ralbii.mm"
include "bitr3i.mm"
include "albii.mm"
include "ralcom4.mm"
include "fvex.mm"
include "breq1.mm"
include "imbi2d.mm"
include "ceqsalv.mm"
include "syl6bb.mm"
include "bitrd.mm"

theorem itg2leub
  let cA: class A
  let vg: setvar g
  let cF: class F
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let vh: setvar h
  let vy: setvar y
  let cG: class G

  disjoint A g
  disjoint F g
  disjoint g x
  disjoint g z
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint g h
  disjoint g y
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint x y
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G g
  disjoint G h
  disjoint G x
  disjoint G y
  disjoint G z
  assert |- ( ( F : RR --> ( 0 [,] +oo ) /\ A e. RR* ) -> ( ( S.2 ` F ) <_ A <-> A. g e. dom S.1 ( g oR <_ F -> ( S.1 ` g ) <_ A ) ) )

  proof
    cr
    cc0
    cpnf
    cicc
    co
    cF
    wf
    #
    cA
    cxr
    wcel
    #
    wa
    #
    cF
    citg2
    cfv
    #
    cA
    cle
    wbr
    vg
    cv
    #
    cF
    cle
    cofr
    wbr
    #
    vx
    cv
    #
    @4
    citg1
    cfv
    #
    wceq
    #
    wa
    #
    vg
    citg1
    cdm
    #
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    #
    cA
    cle
    wbr
    #
    @5
    @7
    cA
    cle
    wbr
    #
    wi
    #
    vg
    @10
    wral
    #
    @2
    @3
    @13
    cA
    cle
    @0
    @3
    @13
    wceq
    @1
    vx
    vg
    cF
    @12
    @12
    eqid
    #
    itg2val
    adantr
    breq1d
    @2
    @14
    vz
    cv
    #
    cA
    cle
    wbr
    #
    vz
    @12
    wral
    #
    @17
    @1
    @14
    @21
    wb
    #
    @0
    @12
    cxr
    wss
    @1
    @22
    vx
    vg
    cF
    @12
    @18
    itg2lcl
    vz
    @12
    cA
    supxrleub
    mpan
    adantl
    @21
    @5
    @19
    @7
    wceq
    #
    wa
    #
    vg
    @10
    wrex
    #
    @20
    wi
    #
    vz
    wal
    #
    @17
    @11
    @25
    @20
    vz
    vx
    @6
    @19
    wceq
    #
    @9
    @24
    vg
    @10
    @28
    @8
    @23
    @5
    @6
    @19
    @7
    eqeq1
    anbi2d
    rexbidv
    ralab
    @27
    @23
    @5
    @20
    wi
    #
    wi
    #
    vg
    @10
    wral
    #
    vz
    wal
    #
    @17
    @26
    @31
    vz
    @26
    @24
    @20
    wi
    #
    vg
    @10
    wral
    @31
    @24
    @20
    vg
    @10
    r19.23v
    @33
    @30
    vg
    @10
    @33
    @23
    @5
    wa
    @20
    wi
    @30
    @5
    @23
    @20
    ancomst
    @23
    @5
    @20
    impexp
    bitri
    ralbii
    bitr3i
    albii
    @32
    @30
    vz
    wal
    #
    vg
    @10
    wral
    @17
    @30
    vg
    vz
    @10
    ralcom4
    @34
    @16
    vg
    @10
    @29
    @16
    vz
    @7
    @4
    citg1
    fvex
    @23
    @20
    @15
    @5
    @19
    @7
    cA
    cle
    breq1
    imbi2d
    ceqsalv
    ralbii
    bitr3i
    bitri
    bitri
    syl6bb
    bitrd
end
