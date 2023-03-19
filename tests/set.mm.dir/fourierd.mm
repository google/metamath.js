include "caddc.mm"
include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "ccos.mm"
include "csin.mm"
include "cmpt.mm"
include "c1.mm"
include "cseq.mm"
include "c2.mm"
include "cdiv.mm"
include "cc0.mm"
include "cmin.mm"
include "cli.mm"
include "wbr.mm"
include "csu.mm"
include "wceq.mm"
include "nfcv.mm"
include "cn0.mm"
include "cpi.mm"
include "cneg.mm"
include "cioo.mm"
include "citg.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfov.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvmpt.mm"
include "fourierdlem115.mm"
include "simprd.mm"

theorem fourierd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cL: class L
  let cX: class X
  let vk: setvar k
  assume fourierd.f: |- ( ph -> F : RR --> RR )
  assume fourierd.t: |- T = ( 2 x. _pi )
  assume fourierd.per: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierd.g: |- G = ( ( RR _D F ) |` ( -u _pi (,) _pi ) )
  assume fourierd.dmdv: |- ( ph -> ( ( -u _pi (,) _pi ) \ dom G ) e. Fin )
  assume fourierd.dvcn: |- ( ph -> G e. ( dom G -cn-> CC ) )
  assume fourierd.rlim: |- ( ( ph /\ x e. ( ( -u _pi [,) _pi ) \ dom G ) ) -> ( ( G |` ( x (,) +oo ) ) limCC x ) =/= (/) )
  assume fourierd.llim: |- ( ( ph /\ x e. ( ( -u _pi (,] _pi ) \ dom G ) ) -> ( ( G |` ( -oo (,) x ) ) limCC x ) =/= (/) )
  assume fourierd.x: |- ( ph -> X e. RR )
  assume fourierd.l: |- ( ph -> L e. ( ( F |` ( -oo (,) X ) ) limCC X ) )
  assume fourierd.r: |- ( ph -> R e. ( ( F |` ( X (,) +oo ) ) limCC X ) )
  assume fourierd.a: |- A = ( n e. NN0 |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( cos ` ( n x. x ) ) ) _d x / _pi ) )
  assume fourierd.b: |- B = ( n e. NN |-> ( S. ( -u _pi (,) _pi ) ( ( F ` x ) x. ( sin ` ( n x. x ) ) ) _d x / _pi ) )

  disjoint F n
  disjoint F x
  disjoint n x
  disjoint G x
  disjoint T x
  disjoint X n
  disjoint X x
  disjoint ph x
  disjoint A k
  disjoint B k
  disjoint F k
  disjoint k n
  disjoint k x
  disjoint G k
  disjoint L k
  disjoint R k
  disjoint T k
  disjoint X k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> ( ( ( A ` 0 ) / 2 ) + sum_ n e. NN ( ( ( A ` n ) x. ( cos ` ( n x. X ) ) ) + ( ( B ` n ) x. ( sin ` ( n x. X ) ) ) ) ) = ( ( L + R ) / 2 ) )

  proof
    wph
    caddc
    vn
    cn
    vn
    cv
    #
    cA
    cfv
    #
    @0
    cX
    cmul
    co
    #
    ccos
    cfv
    #
    cmul
    co
    #
    @0
    cB
    cfv
    #
    @2
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    c1
    cseq
    cL
    cR
    caddc
    co
    c2
    cdiv
    co
    #
    cc0
    cA
    cfv
    c2
    cdiv
    co
    #
    cmin
    co
    cli
    wbr
    @11
    cn
    @8
    vn
    csu
    caddc
    co
    @10
    wceq
    wph
    vx
    cA
    cB
    cR
    @9
    cT
    vk
    vn
    cF
    cG
    cL
    cX
    fourierd.f
    fourierd.t
    fourierd.per
    fourierd.g
    fourierd.dmdv
    fourierd.dvcn
    fourierd.rlim
    fourierd.llim
    fourierd.x
    fourierd.l
    fourierd.r
    fourierd.a
    fourierd.b
    vn
    vk
    cn
    @8
    vk
    cv
    #
    cA
    cfv
    #
    @12
    cX
    cmul
    co
    #
    ccos
    cfv
    #
    cmul
    co
    #
    @12
    cB
    cfv
    #
    @14
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    vk
    @8
    nfcv
    vn
    @16
    @19
    caddc
    vn
    @13
    @15
    cmul
    vn
    @12
    cA
    vn
    cA
    vn
    cn0
    vx
    cpi
    cneg
    cpi
    cioo
    co
    #
    vx
    cv
    #
    cF
    cfv
    #
    @0
    @21
    cmul
    co
    #
    ccos
    cfv
    cmul
    co
    citg
    cpi
    cdiv
    co
    #
    cmpt
    fourierd.a
    vn
    cn0
    @24
    nfmpt1
    nfcxfr
    vn
    @12
    nfcv
    #
    nffv
    vn
    cmul
    nfcv
    #
    vn
    @15
    nfcv
    nfov
    vn
    caddc
    nfcv
    vn
    @17
    @18
    cmul
    vn
    @12
    cB
    vn
    cB
    vn
    cn
    vx
    @20
    @22
    @23
    csin
    cfv
    cmul
    co
    citg
    cpi
    cdiv
    co
    #
    cmpt
    fourierd.b
    vn
    cn
    @27
    nfmpt1
    nfcxfr
    @25
    nffv
    @26
    vn
    @18
    nfcv
    nfov
    nfov
    @0
    @12
    wceq
    #
    @4
    @16
    @7
    @19
    caddc
    @28
    @1
    @13
    @3
    @15
    cmul
    @0
    @12
    cA
    fveq2
    @28
    @2
    @14
    ccos
    @0
    @12
    cX
    cmul
    oveq1
    #
    fveq2d
    oveq12d
    @28
    @5
    @17
    @6
    @18
    cmul
    @0
    @12
    cB
    fveq2
    @28
    @2
    @14
    csin
    @29
    fveq2d
    oveq12d
    oveq12d
    cbvmpt
    fourierdlem115
    simprd
end
