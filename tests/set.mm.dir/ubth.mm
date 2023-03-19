include "ccbn.mm"
include "wcel.mm"
include "cnv.mm"
include "cblo.mm"
include "co.mm"
include "wss.mm"
include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wb.mm"
include "wi.mm"
include "caddc.mm"
include "cmul.mm"
include "cop.mm"
include "cabs.mm"
include "cif.mm"
include "cba.mm"
include "cnmoo.mm"
include "cnmcv.mm"
include "wceq.mm"
include "oveq1.mm"
include "sseq2d.mm"
include "fveq2.mm"
include "syl5eq.mm"
include "raleqdv.mm"
include "fveq1d.mm"
include "breq1d.mm"
include "rexralbidv.mm"
include "bibi12d.mm"
include "imbi12d.mm"
include "oveq2.mm"
include "ralbidv.mm"
include "cims.mm"
include "cmopn.mm"
include "eqid.mm"
include "cnbn.mm"
include "elimel.mm"
include "elimnvu.mm"
include "id.mm"
include "ubthlem3.mm"
include "dedth2h.mm"
include "3impia.mm"

theorem ubth
  let vx: setvar x
  let vt: setvar t
  let cT: class T
  let cU: class U
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cD: class D
  let cJ: class J
  let cK: class K
  let vm: setvar m
  let vu: setvar u
  let cP: class P
  let wph: wff ph
  let cR: class R
  assume ubth.1: |- X = ( BaseSet ` U )
  assume ubth.2: |- N = ( normCV ` W )
  assume ubth.3: |- M = ( U normOpOLD W )

  disjoint c x
  disjoint c t
  disjoint t x
  disjoint d t
  disjoint d x
  disjoint c d
  disjoint N c
  disjoint N d
  disjoint N t
  disjoint N x
  disjoint T c
  disjoint T d
  disjoint T t
  disjoint T x
  disjoint U c
  disjoint U d
  disjoint U t
  disjoint U x
  disjoint W c
  disjoint W d
  disjoint W t
  disjoint W x
  disjoint X c
  disjoint X d
  disjoint X t
  disjoint X x
  disjoint c k
  disjoint c n
  disjoint c r
  disjoint c y
  disjoint c z
  disjoint A c
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint D c
  disjoint k t
  disjoint D k
  disjoint n t
  disjoint D n
  disjoint r t
  disjoint D r
  disjoint t z
  disjoint D t
  disjoint D x
  disjoint D z
  disjoint J k
  disjoint J n
  disjoint t y
  disjoint J t
  disjoint J x
  disjoint J y
  disjoint d k
  disjoint d z
  disjoint K d
  disjoint K k
  disjoint K t
  disjoint K x
  disjoint K z
  disjoint c m
  disjoint c u
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d u
  disjoint d y
  disjoint k m
  disjoint k u
  disjoint N k
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m u
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint N m
  disjoint n u
  disjoint N n
  disjoint r u
  disjoint N r
  disjoint t u
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint N u
  disjoint N y
  disjoint N z
  disjoint P t
  disjoint P z
  disjoint c ph
  disjoint k ph
  disjoint n ph
  disjoint ph r
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint R d
  disjoint R t
  disjoint R x
  disjoint R z
  disjoint T k
  disjoint T m
  disjoint T n
  disjoint T r
  disjoint T u
  disjoint T y
  disjoint T z
  disjoint U n
  disjoint U r
  disjoint U y
  disjoint U z
  disjoint W n
  disjoint W r
  disjoint W y
  disjoint X k
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X y
  disjoint X z
  assert |- ( ( U e. CBan /\ W e. NrmCVec /\ T C_ ( U BLnOp W ) ) -> ( A. x e. X E. c e. RR A. t e. T ( N ` ( t ` x ) ) <_ c <-> E. d e. RR A. t e. T ( M ` t ) <_ d ) )

  proof
    cU
    ccbn
    wcel
    #
    cW
    cnv
    wcel
    #
    cT
    cU
    cW
    cblo
    co
    #
    wss
    #
    vx
    cv
    vt
    cv
    #
    cfv
    #
    cN
    cfv
    #
    vc
    cv
    #
    cle
    wbr
    #
    vt
    cT
    wral
    vc
    cr
    wrex
    #
    vx
    cX
    wral
    #
    @4
    cM
    cfv
    #
    vd
    cv
    #
    cle
    wbr
    #
    vt
    cT
    wral
    vd
    cr
    wrex
    #
    wb
    #
    @0
    @1
    @3
    @15
    wi
    cT
    @0
    cU
    caddc
    cmul
    cop
    cabs
    cop
    #
    cif
    #
    cW
    cblo
    co
    #
    wss
    #
    @9
    vx
    @17
    cba
    cfv
    #
    wral
    #
    @4
    @17
    cW
    cnmoo
    co
    #
    cfv
    #
    @12
    cle
    wbr
    #
    vt
    cT
    wral
    vd
    cr
    wrex
    #
    wb
    #
    wi
    cT
    @17
    @1
    cW
    @16
    cif
    #
    cblo
    co
    #
    wss
    #
    @5
    @27
    cnmcv
    cfv
    #
    cfv
    #
    @7
    cle
    wbr
    #
    vt
    cT
    wral
    vc
    cr
    wrex
    #
    vx
    @20
    wral
    #
    @4
    @17
    @27
    cnmoo
    co
    #
    cfv
    #
    @12
    cle
    wbr
    #
    vt
    cT
    wral
    vd
    cr
    wrex
    #
    wb
    #
    wi
    cU
    cW
    @16
    @16
    cU
    @17
    wceq
    #
    @3
    @19
    @15
    @26
    @40
    @2
    @18
    cT
    cU
    @17
    cW
    cblo
    oveq1
    sseq2d
    @40
    @10
    @21
    @14
    @25
    @40
    @9
    vx
    cX
    @20
    @40
    cX
    cU
    cba
    cfv
    @20
    ubth.1
    cU
    @17
    cba
    fveq2
    syl5eq
    raleqdv
    @40
    @13
    @24
    vd
    vt
    cr
    cT
    @40
    @11
    @23
    @12
    cle
    @40
    @4
    cM
    @22
    @40
    cM
    cU
    cW
    cnmoo
    co
    @22
    ubth.3
    cU
    @17
    cW
    cnmoo
    oveq1
    syl5eq
    fveq1d
    breq1d
    rexralbidv
    bibi12d
    imbi12d
    cW
    @27
    wceq
    #
    @19
    @29
    @26
    @39
    @41
    @18
    @28
    cT
    cW
    @27
    @17
    cblo
    oveq2
    sseq2d
    @41
    @21
    @34
    @25
    @38
    @41
    @9
    @33
    vx
    @20
    @41
    @8
    @32
    vc
    vt
    cr
    cT
    @41
    @6
    @31
    @7
    cle
    @41
    @5
    cN
    @30
    @41
    cN
    cW
    cnmcv
    cfv
    @30
    ubth.2
    cW
    @27
    cnmcv
    fveq2
    syl5eq
    fveq1d
    breq1d
    rexralbidv
    ralbidv
    @41
    @24
    @37
    vd
    vt
    cr
    cT
    @41
    @23
    @36
    @12
    cle
    @41
    @4
    @22
    @35
    cW
    @27
    @17
    cnmoo
    oveq2
    fveq1d
    breq1d
    rexralbidv
    bibi12d
    imbi12d
    @29
    vx
    vt
    @17
    cims
    cfv
    #
    cT
    @17
    @42
    cmopn
    cfv
    #
    @30
    @27
    @20
    vc
    vd
    @20
    eqid
    @30
    eqid
    @42
    eqid
    @43
    eqid
    cU
    @16
    ccbn
    @16
    @16
    eqid
    cnbn
    elimel
    cW
    elimnvu
    @29
    id
    ubthlem3
    dedth2h
    3impia
end
