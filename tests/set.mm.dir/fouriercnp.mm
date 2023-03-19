include "cc0.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cn.mm"
include "cv.mm"
include "cmul.mm"
include "ccos.mm"
include "csin.mm"
include "caddc.mm"
include "csu.mm"
include "ccnp.mm"
include "wcel.mm"
include "cr.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cuni.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "cnprcl.mm"
include "syl.mm"
include "climc.mm"
include "cmnf.mm"
include "cres.mm"
include "limcresi.mm"
include "cc.mm"
include "wf.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "wa.mm"
include "crest.mm"
include "eqid.mm"
include "tgioo2.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "fveq1i.mm"
include "syl6eleq.mm"
include "ctop.mm"
include "wss.mm"
include "wb.mm"
include "cnfldtop.mm"
include "a1i.mm"
include "ax-resscn.mm"
include "unicntop.mm"
include "cnprest2.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "cnplimc.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simprd.mm"
include "sseldi.mm"
include "cpnf.mm"
include "fourierd.mm"
include "ffvelrnd.mm"
include "recnd.mm"
include "2timesd.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan3d.mm"
include "3eqtrd.mm"

theorem fouriercnp
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let vk: setvar k
  assume fouriercnp.f: |- ( ph -> F : RR --> RR )
  assume fouriercnp.t: |- T = ( 2 x. _pi )
  assume fouriercnp.per: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fouriercnp.g: |- G = ( ( RR _D F ) |` ( -u _pi (,) _pi ) )
  assume fouriercnp.dmdv: |- ( ph -> ( ( -u _pi (,) _pi ) \ dom G ) e. Fin )
  assume fouriercnp.dvcn: |- ( ph -> G e. ( dom G -cn-> CC ) )
  assume fouriercnp.rlim: |- ( ( ph /\ x e. ( ( -u _pi [,) _pi ) \ dom G ) ) -> ( ( G |` ( x (,) +oo ) ) limCC x ) =/= (/) )
  assume fouriercnp.llim: |- ( ( ph /\ x e. ( ( -u _pi (,] _pi ) \ dom G ) ) -> ( ( G |` ( -oo (,) x ) ) limCC x ) =/= (/) )
  assume fouriercnp.j: |- J = ( topGen ` ran (,) )
  assume fouriercnp.cnp: |- ( ph -> F e. ( ( J CnP J ) ` X ) )
  assume fouriercnp.a: |- A = ( n e. NN0 |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( cos ` ( n x. x ) ) ) _d x / _pi ) )
  assume fouriercnp.b: |- B = ( n e. NN |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( sin ` ( n x. x ) ) ) _d x / _pi ) )

  disjoint F n
  disjoint F x
  disjoint n x
  disjoint G x
  disjoint T x
  disjoint X n
  disjoint X x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( ( ( A ` 0 ) / 2 ) + sum_ n e. NN ( ( ( A ` n ) x. ( cos ` ( n x. X ) ) ) + ( ( B ` n ) x. ( sin ` ( n x. X ) ) ) ) ) = ( F ` X ) )

  proof
    wph
    cc0
    cA
    cfv
    c2
    cdiv
    co
    cn
    vn
    cv
    #
    cA
    cfv
    @0
    cX
    cmul
    co
    #
    ccos
    cfv
    cmul
    co
    @0
    cB
    cfv
    @1
    csin
    cfv
    cmul
    co
    caddc
    co
    vn
    csu
    caddc
    co
    cX
    cF
    cfv
    #
    @2
    caddc
    co
    #
    c2
    cdiv
    co
    c2
    @2
    cmul
    co
    #
    c2
    cdiv
    co
    @2
    wph
    vx
    cA
    cB
    @2
    cT
    vn
    cF
    cG
    @2
    cX
    fouriercnp.f
    fouriercnp.t
    fouriercnp.per
    fouriercnp.g
    fouriercnp.dmdv
    fouriercnp.dvcn
    fouriercnp.rlim
    fouriercnp.llim
    wph
    cF
    cX
    cJ
    cJ
    ccnp
    co
    #
    cfv
    #
    wcel
    cX
    cr
    wcel
    #
    fouriercnp.cnp
    cX
    cF
    cJ
    cJ
    cr
    cr
    cioo
    crn
    ctg
    cfv
    #
    cuni
    cJ
    cuni
    uniretop
    cJ
    @8
    fouriercnp.j
    unieqi
    eqtr4i
    #
    cnprcl
    syl
    #
    wph
    cF
    cX
    climc
    co
    #
    cF
    cmnf
    cX
    cioo
    co
    #
    cres
    cX
    climc
    co
    @2
    cX
    @12
    cF
    limcresi
    wph
    cr
    cc
    cF
    wf
    #
    @2
    @11
    wcel
    #
    wph
    cF
    cX
    cJ
    ccnfld
    ctopn
    cfv
    #
    ccnp
    co
    cfv
    wcel
    #
    @13
    @14
    wa
    #
    wph
    @16
    cF
    cX
    cJ
    @15
    cr
    crest
    co
    #
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    wph
    cF
    @6
    @20
    fouriercnp.cnp
    cX
    @5
    @19
    cJ
    @18
    cJ
    ccnp
    cJ
    @8
    @18
    fouriercnp.j
    @15
    @15
    eqid
    #
    tgioo2
    eqtri
    #
    oveq2i
    fveq1i
    syl6eleq
    wph
    @15
    ctop
    wcel
    #
    cr
    cr
    cF
    wf
    cr
    cc
    wss
    #
    @16
    @21
    wb
    @24
    wph
    @15
    @22
    cnfldtop
    a1i
    fouriercnp.f
    @25
    wph
    ax-resscn
    a1i
    cr
    cX
    cF
    cJ
    @15
    cr
    cc
    @9
    unicntop
    cnprest2
    syl3anc
    mpbird
    wph
    @25
    @7
    @16
    @17
    wb
    ax-resscn
    @10
    cr
    cX
    cF
    cJ
    @15
    @22
    @23
    cnplimc
    sylancr
    mpbid
    simprd
    #
    sseldi
    wph
    @11
    cF
    cX
    cpnf
    cioo
    co
    #
    cres
    cX
    climc
    co
    @2
    cX
    @27
    cF
    limcresi
    @26
    sseldi
    fouriercnp.a
    fouriercnp.b
    fourierd
    wph
    @3
    @4
    c2
    cdiv
    wph
    @4
    @3
    wph
    @2
    wph
    @2
    wph
    cr
    cr
    cX
    cF
    fouriercnp.f
    @10
    ffvelrnd
    recnd
    #
    2timesd
    eqcomd
    oveq1d
    wph
    @2
    c2
    @28
    wph
    2cnd
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    divcan3d
    3eqtrd
end
