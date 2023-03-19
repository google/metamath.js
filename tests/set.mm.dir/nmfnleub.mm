include "chil.mm"
include "cc.mm"
include "wf.mm"
include "cxr.mm"
include "wcel.mm"
include "wa.mm"
include "cnmf.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cno.mm"
include "c1.mm"
include "cabs.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "clt.mm"
include "csup.mm"
include "wi.mm"
include "wral.mm"
include "nmfnval.mm"
include "adantr.mm"
include "breq1d.mm"
include "wss.mm"
include "wb.mm"
include "cr.mm"
include "nmfnsetre.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrleub.mm"
include "sylan.mm"
include "wal.mm"
include "ancom.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "rexbidv.mm"
include "ralab.mm"
include "ralcom4.mm"
include "impexp.mm"
include "albii.mm"
include "fvex.mm"
include "breq1.mm"
include "imbi2d.mm"
include "ceqsalv.mm"
include "bitri.mm"
include "ralbii.mm"
include "r19.23v.mm"
include "3bitr3i.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "bitrd.mm"

theorem nmfnleub
  let vx: setvar x
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S

  disjoint A x
  disjoint T x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T y
  disjoint T z
  disjoint T w
  assert |- ( ( T : ~H --> CC /\ A e. RR* ) -> ( ( normfn ` T ) <_ A <-> A. x e. ~H ( ( normh ` x ) <_ 1 -> ( abs ` ( T ` x ) ) <_ A ) ) )

  proof
    chil
    cc
    cT
    wf
    #
    cA
    cxr
    wcel
    #
    wa
    #
    cT
    cnmf
    cfv
    #
    cA
    cle
    wbr
    vx
    cv
    #
    cno
    cfv
    c1
    cle
    wbr
    #
    vy
    cv
    #
    @4
    cT
    cfv
    #
    cabs
    cfv
    #
    wceq
    #
    wa
    #
    vx
    chil
    wrex
    #
    vy
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
    @8
    cA
    cle
    wbr
    #
    wi
    #
    vx
    chil
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
    vy
    vx
    cT
    nmfnval
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
    @0
    @12
    cxr
    wss
    @1
    @14
    @20
    wb
    @0
    @12
    cr
    cxr
    vy
    vx
    cT
    nmfnsetre
    ressxr
    syl6ss
    vz
    @12
    cA
    supxrleub
    sylan
    @20
    @18
    @8
    wceq
    #
    @5
    wa
    #
    vx
    chil
    wrex
    #
    @19
    wi
    #
    vz
    wal
    #
    @17
    @11
    @23
    @19
    vz
    vy
    @6
    @18
    wceq
    #
    @10
    @22
    vx
    chil
    @10
    @9
    @5
    wa
    @26
    @22
    @5
    @9
    ancom
    @26
    @9
    @21
    @5
    @6
    @18
    @8
    eqeq1
    anbi1d
    syl5bb
    rexbidv
    ralab
    @22
    @19
    wi
    #
    vz
    wal
    #
    vx
    chil
    wral
    @27
    vx
    chil
    wral
    #
    vz
    wal
    @17
    @25
    @27
    vx
    vz
    chil
    ralcom4
    @28
    @16
    vx
    chil
    @28
    @21
    @5
    @19
    wi
    #
    wi
    #
    vz
    wal
    @16
    @27
    @31
    vz
    @21
    @5
    @19
    impexp
    albii
    @30
    @16
    vz
    @8
    @7
    cabs
    fvex
    @21
    @19
    @15
    @5
    @18
    @8
    cA
    cle
    breq1
    imbi2d
    ceqsalv
    bitri
    ralbii
    @29
    @24
    vz
    @22
    @19
    vx
    chil
    r19.23v
    albii
    3bitr3i
    bitr4i
    syl6bb
    bitrd
end
