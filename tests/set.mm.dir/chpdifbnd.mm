include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cchp.mm"
include "cfv.mm"
include "clog.mm"
include "cmul.mm"
include "co.mm"
include "cfl.mm"
include "cfz.mm"
include "cvma.mm"
include "cdiv.mm"
include "csu.mm"
include "caddc.mm"
include "c2.mm"
include "cmin.mm"
include "cabs.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cicc.mm"
include "cioo.mm"
include "selberg2b.mm"
include "simpl.mm"
include "cc0.mm"
include "0red.mm"
include "1red.mm"
include "clt.mm"
include "0lt1.mm"
include "a1i.mm"
include "simpr.mm"
include "ltletrd.mm"
include "elrpd.mm"
include "adantr.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "eqid.mm"
include "chpdifbndlem2.mm"
include "rexlimdvaa.mm"
include "mpi.mm"

theorem chpdifbnd
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vc: setvar c
  let vb: setvar b
  let vn: setvar n
  let vz: setvar z

  disjoint c x
  disjoint c y
  disjoint A c
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint b c
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint c n
  disjoint c z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x z
  disjoint y z
  disjoint A z
  assert |- ( ( A e. RR /\ 1 <_ A ) -> E. c e. RR+ A. x e. ( 1 (,) +oo ) A. y e. ( x [,] ( A x. x ) ) ( ( psi ` y ) - ( psi ` x ) ) <_ ( ( 2 x. ( y - x ) ) + ( c x. ( x / ( log ` x ) ) ) ) )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    wa
    #
    vz
    cv
    #
    cchp
    cfv
    @3
    clog
    cfv
    #
    cmul
    co
    c1
    @3
    cfl
    cfv
    cfz
    co
    vn
    cv
    #
    cvma
    cfv
    @3
    @5
    cdiv
    co
    cchp
    cfv
    cmul
    co
    vn
    csu
    caddc
    co
    @3
    cdiv
    co
    c2
    @4
    cmul
    co
    cmin
    co
    cabs
    cfv
    vb
    cv
    #
    cle
    wbr
    vz
    c1
    cpnf
    cico
    co
    wral
    #
    vb
    crp
    wrex
    vy
    cv
    #
    cchp
    cfv
    vx
    cv
    #
    cchp
    cfv
    cmin
    co
    c2
    @8
    @9
    cmin
    co
    cmul
    co
    vc
    cv
    @9
    @9
    clog
    cfv
    cdiv
    co
    cmul
    co
    caddc
    co
    cle
    wbr
    vy
    @9
    cA
    @9
    cmul
    co
    cicc
    co
    wral
    vx
    c1
    cpnf
    cioo
    co
    wral
    vc
    crp
    wrex
    #
    vz
    vn
    vb
    selberg2b
    @2
    @7
    @10
    vb
    crp
    @2
    @6
    crp
    wcel
    #
    @7
    wa
    #
    wa
    vx
    vy
    vz
    cA
    @6
    @6
    cA
    c1
    caddc
    co
    cmul
    co
    c2
    cA
    cmul
    co
    cA
    clog
    cfv
    cmul
    co
    caddc
    co
    #
    vn
    vc
    @2
    cA
    crp
    wcel
    @12
    @2
    cA
    @0
    @1
    simpl
    #
    @2
    cc0
    c1
    cA
    @2
    0red
    @2
    1red
    @14
    cc0
    c1
    clt
    wbr
    @2
    0lt1
    a1i
    @0
    @1
    simpr
    ltletrd
    elrpd
    adantr
    @0
    @1
    @12
    simplr
    @2
    @11
    @7
    simprl
    @2
    @11
    @7
    simprr
    @13
    eqid
    chpdifbndlem2
    rexlimdvaa
    mpi
end
